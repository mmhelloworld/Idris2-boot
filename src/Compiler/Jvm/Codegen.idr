module Compiler.Jvm.Codegen

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.Bool.Extra
import Data.List
import Data.SortedMap
import Data.Vect

import Core.Directory
import Core.Options
import Utils.Hex

import Data.NameMap

import System.Info

import IdrisJvm.IO
import IdrisJvm.File
import IdrisJvm.System
import Java.Lang

import Compiler.Jvm.Asm
import Compiler.Jvm.MockAsm
import Compiler.Jvm.Optimizer
import Compiler.Jvm.InferredType
import Compiler.Jvm.Jname
import Compiler.Jvm.Jvar
import Compiler.Jvm.Variable
import Compiler.Jvm.Tree
import Compiler.Jvm.FunctionTree
import Compiler.Jvm.ExtPrim
import Compiler.Jvm.ShowUtil
import Compiler.Jvm.Tuples

%default covering
%hide Java.Lang.JavaString.stringClass

addScopeLocalVariables : Scope -> Asm ()
addScopeLocalVariables scope = do
    let scopeIndex = index scope
    let (lineNumberStart, lineNumberEnd) = lineNumbers scope
    let (labelStart, labelEnd) = labels scope
    go labelStart labelEnd $ SortedMap.toList $ variableIndices scope
  where
    go : String -> String -> List (String, Nat) -> Asm ()
    go _ _ [] = Pure ()
    go labelStart labelEnd ((name, varIndex) :: rest) = do
        variableType <- getVariableTypeAtScope (index scope) name
        LocalVariable name (getJvmTypeDescriptor variableType) Nothing labelStart labelEnd varIndex
        go labelStart labelEnd rest

addLocalVariables : Nat -> Asm ()
addLocalVariables scopeIndex = do
    scope <- getScope scopeIndex
    addScopeLocalVariables scope
    traverse_ addLocalVariables $ childIndices scope

enterScope : Asm ()
enterScope = do
    scopeIndex <- newScopeIndex
    updateCurrentScopeIndex scopeIndex
    scope <- getScope scopeIndex
    Debug $ "Entering scope " ++ show scope

exitScope : Scope -> Asm ()
exitScope targetScope = do
    Debug $ "Exiting scope " ++ show !(getScope !getCurrentScopeIndex)
    updateCurrentScopeIndex $ index targetScope

withScope : Lazy (Asm ()) -> Asm ()
withScope op = do
    scope <- getScope !getCurrentScopeIndex
    enterScope
    op
    exitScope scope

methodStartLabel : String
methodStartLabel = "methodStartLabel"

methodEndLabel : String
methodEndLabel = "methodEndLabel"

defaultValue : InferredType -> Asm ()
defaultValue IBool = Iconst 0
defaultValue IByte = Iconst 0
defaultValue IChar = Iconst 0
defaultValue IShort = Iconst 0
defaultValue IInt = Iconst 0
defaultValue ILong = Lconst 0
defaultValue IFloat = Fconst 0
defaultValue IDouble = Dconst 0
defaultValue _ = Aconstnull

multiValueMap : Ord k => (a -> k) -> (a -> v) -> List a -> SortedMap k (List v)
multiValueMap f g xs = go SortedMap.empty xs where
  go : SortedMap k (List v) -> List a -> SortedMap k (List v)
  go acc [] = acc
  go acc (x :: xs) =
    let key = f x
        value = g x
        vs = fromMaybe [] $ SortedMap.lookup key acc
        newAcc = SortedMap.insert key (value :: vs) acc
    in go newAcc xs

constantAltIntExpr : FC -> NamedConstAlt -> Asm (String, Int, NamedConstAlt)
constantAltIntExpr fc alt@(MkNConstAlt constant _) = do
        constExpr <- getIntConstantValue fc constant
        label <- newLabel
        Pure (label, constExpr, alt)

hashCode : TT.Constant -> Asm (Maybe Int)
hashCode (BI value) = LiftIo $ (Just <$> invokeInstance "hashCode" (Integer -> JVM_IO Int) value)
hashCode (Str value) = LiftIo $ (Just <$> invokeInstance "hashCode" (String -> JVM_IO Int) value)
hashCode x = Pure Nothing

getHashCodeSwitchClass : FC -> InferredType -> Asm String
getHashCodeSwitchClass fc constantType =
    if constantType == inferredStringType then Pure stringClass
    else if constantType == inferredBigIntegerType then Pure bigIntegerClass
    else Throw fc ("Constant type " ++ show constantType ++ " cannot be compiled to 'Switch'.")

assembleHashCodeSwitchConstant : FC -> TT.Constant -> Asm ()
assembleHashCodeSwitchConstant _ (BI value) = newBigInteger $ show value
assembleHashCodeSwitchConstant _ (Str value) = Ldc $ StringConst value
assembleHashCodeSwitchConstant fc constant =
    Throw fc $ "Constant " ++ show constant ++ " cannot be compiled to 'switch'"

conAltIntExpr : NamedConAlt -> Asm (String, Int, NamedConAlt)
conAltIntExpr alt@(MkNConAlt name tag _ expr) = do
    label <- newLabel
    intValue <- maybe (Throw emptyFC $ "Missing constructor tag " ++ show name) Pure tag
    Pure (label, intValue, alt)

conAltStringExpr : NamedConAlt -> Asm (String, String, NamedConAlt)
conAltStringExpr alt@(MkNConAlt name tag _ expr) = do
    label <- newLabel
    Pure (label, jvmSimpleName name, alt)

createDefaultLabel : Asm String
createDefaultLabel = do
    label <- newLabel
    CreateLabel label
    Pure label

getSwitchCasesWithEndLabel : List (String, Int, a) -> List String -> List (String, Int, a, String)
getSwitchCasesWithEndLabel switchCases labelStarts = go $ List.zip switchCases (drop 1 labelStarts ++ [methodEndLabel])
    where
        go : List ((String, Int, a), String) -> List (String, Int, a, String)
        go (((labelStart, constExpr, body), labelEnd) :: xs) = (labelStart, constExpr, body, labelEnd) :: go xs
        go [] = []

labelHashCodeAlt : (Int, a) -> Asm (String, Int, a)
labelHashCodeAlt (hash, expressions) = Pure (!newLabel, hash, expressions)

getHashCodeCasesWithLabels : SortedMap Int (List (Nat, a)) ->
    Asm (List (String, Int, List (Nat, a)))
getHashCodeCasesWithLabels positionAndAltsByHash = traverse labelHashCodeAlt $ SortedMap.toList positionAndAltsByHash

mutual
    assembleExpr : (ret : Asm ()) -> InferredType -> NamedCExp -> Asm ()

    assembleExpr ret returnType (NmDelay _ expr) = assembleSubMethodWithScope ret returnType Nothing Nothing expr

    assembleExpr ret returnType (NmLocal _ loc) = do
        let variableName = jvmSimpleName loc
        index <- getVariableIndex variableName
        variableType <- getVariableType variableName
        loadVar !getVariableTypes variableType returnType index
        ret

    assembleExpr ret returnType (NmApp _ (NmLam _ var body) [argument]) =
        assembleSubMethodWithScope ret returnType (Just argument) (Just var) body
    assembleExpr ret returnType (NmLam _ parameter body) =
        assembleSubMethodWithScope ret returnType Nothing (Just parameter) body

    assembleExpr ret returnType (NmLet _ var value expr) = do
        valueScopeStartLabel <- newLabel
        CreateLabel valueScopeStartLabel
        targetExprScopeStartLabel <- newLabel
        CreateLabel targetExprScopeStartLabel
        letScopeIndex <- getCurrentScopeIndex
        let variableName = jvmSimpleName var
        variableType <- getVariableType variableName
        variableIndex <- getVariableIndex variableName

        withScope $ do
            valueScopeIndex <- getCurrentScopeIndex
            scope <- getScope valueScopeIndex
            let (lineNumberStart, lineNumberEnd) = lineNumbers scope
            updateScopeStartLabel valueScopeIndex valueScopeStartLabel
            updateScopeEndLabel valueScopeIndex targetExprScopeStartLabel
            LabelStart valueScopeStartLabel
            addLineNumber lineNumberStart valueScopeStartLabel
            assembleExpr (storeVar variableType variableType variableIndex) variableType value

        withScope $ do
            targetExprScopeIndex <- getCurrentScopeIndex
            scope <- getScope targetExprScopeIndex
            let (lineNumberStart, lineNumberEnd) = lineNumbers scope
            updateScopeStartLabel targetExprScopeIndex targetExprScopeStartLabel
            LabelStart targetExprScopeStartLabel
            addLineNumber lineNumberStart targetExprScopeStartLabel
            updateScopeEndLabel targetExprScopeIndex methodEndLabel
            assembleExpr ret returnType expr

    -- Tail recursion. Store arguments and recur to the beginning of the method
    assembleExpr _ returnType app@(NmApp fc (NmRef nameFc (UN ":__jvmTailRec__:")) args) =
        case length args of
            Z => Goto methodStartLabel
            (S lastArgIndex) => do
                jname <- idrisName <$> getCurrentFunction
                parameterTypes <- getFunctionParameterTypes jname
                let argsWithTypes = List.zip args parameterTypes
                traverse_ storeParameter $ List.zip [0 .. lastArgIndex] argsWithTypes
                Goto methodStartLabel

    assembleExpr ret returnType (NmApp _ (NmRef _ idrisName) args) = do
        -- Not a tail call, unwrap possible trampoline thunks
        let jname = jvmName idrisName
        functionName <- getJvmMethodNameForIdrisName jname
        parameterTypes <- getFunctionParameterTypes jname
        let argsWithTypes = List.zip args parameterTypes
        traverse assembleParameter argsWithTypes
        methodReturnType <- getFunctionReturnType jname
        let methodDescriptor = getMethodDescriptor $ MkInferredFunctionType methodReturnType parameterTypes
        InvokeMethod InvokeStatic (className functionName) (methodName functionName) methodDescriptor False
        asmCast methodReturnType returnType
        ret

    assembleExpr ret returnType (NmApp _ lambdaVariable [arg]) =
        assembleExpr ret1 inferredLambdaType lambdaVariable where
            ret2 : Asm ()
            ret2 = do
                InvokeMethod InvokeInterface "java/util/function/Function" "apply"
                    "(Ljava/lang/Object;)Ljava/lang/Object;" True
                asmCast inferredObjectType returnType
                ret

            ret1 : Asm ()
            ret1 = assembleExpr ret2 inferredObjectType arg

    assembleExpr ret returnType expr@(NmCon fc name tag args) = do
        let fileName = fst $ getSourceLocation expr
        let constructorClassName = jvmSimpleName name
        let constructorType = maybe inferredStringType (const IInt) tag
        New constructorClassName
        Dup
        maybe (Ldc . StringConst $ constructorClassName) Iconst tag
        let constructorParameterCount = length args
        let constructorTypes = constructorType :: replicate constructorParameterCount inferredObjectType
        let argsWithTypes = List.zip args $ drop 1 constructorTypes
        traverse assembleParameter argsWithTypes
        let descriptor = getMethodDescriptor $ MkInferredFunctionType IVoid constructorTypes
        CreateIdrisConstructorClass constructorClassName (isNothing tag) constructorParameterCount
        InvokeMethod InvokeSpecial constructorClassName "<init>" descriptor False
        asmCast (IRef constructorClassName) returnType
        ret

    assembleExpr ret returnType (NmOp fc fn args) = assembleExprOp ret returnType fc fn args
    assembleExpr ret returnType (NmExtPrim fc p args) = jvmExtPrim ret returnType (toPrim p) args
    assembleExpr ret returnType (NmForce _ expr) = assembleExpr ret1 delayedType expr where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeStatic runtimeClass "force" "(Ljava/lang/Object;)Ljava/lang/Object;" False
            asmCast inferredObjectType returnType
            ret

    assembleExpr ret returnType (NmConCase fc sc [] Nothing) = do defaultValue returnType; ret
    assembleExpr ret returnType (NmConCase fc sc [] (Just expr)) = do
        assembleConstructorSwitchExpr sc
        assembleExpr ret returnType expr
    assembleExpr ret returnType (NmConCase fc sc [MkNConAlt name _ args expr] Nothing) = do
        idrisObjectVariableIndex <- assembleConstructorSwitchExpr sc
        assembleConCaseExpr ret returnType idrisObjectVariableIndex name args expr
    assembleExpr ret returnType (NmConCase fc sc alts def) = do
        idrisObjectVariableIndex <- assembleConstructorSwitchExpr sc
        let hasTypeCase = any isTypeCase alts
        let constructorType = if hasTypeCase then "Ljava/lang/String;" else "I"
        loadVar !getVariableTypes idrisObjectType idrisObjectType idrisObjectVariableIndex
        let constructorGetter = if hasTypeCase then "getStringConstructorId" else "getConstructorId"
        InvokeMethod InvokeInterface idrisObjectClass constructorGetter ("()" ++ constructorType) True
        if hasTypeCase then
            assembleStringConstructorSwitch ret returnType fc idrisObjectVariableIndex alts def
        else assembleConstructorSwitch ret returnType fc idrisObjectVariableIndex alts def

    assembleExpr ret returnType (NmConstCase fc sc [] Nothing) = do defaultValue returnType; ret
    assembleExpr ret returnType (NmConstCase fc sc [] (Just expr)) = assembleExpr ret returnType expr
    assembleExpr ret returnType (NmConstCase fc sc alts@(_ :: _) def) = do
        constantType <- getConstantType alts
        assembleConstantSwitch ret returnType constantType fc sc alts def

    assembleExpr ret returnType (NmPrimVal fc (I value)) = do Iconst value; asmCast IInt returnType; ret
    assembleExpr ret returnType (NmPrimVal fc (BI value)) = do
        loadBigInteger $ show value
        asmCast inferredBigIntegerType returnType
        ret
    assembleExpr ret returnType (NmPrimVal fc (Str value)) = do
        Ldc $ StringConst value
        asmCast inferredStringType returnType
        ret
    assembleExpr ret returnType (NmPrimVal fc (Ch value)) = do Iconst (cast value); asmCast IChar returnType; ret
    assembleExpr ret returnType (NmPrimVal fc (Db value)) = do Ldc $ DoubleConst value; asmCast IDouble returnType; ret
    assembleExpr ret returnType (NmPrimVal fc WorldVal) = do Aconstnull; ret
    assembleExpr ret IInt (NmErased fc) = do Iconst 0; ret
    assembleExpr ret IChar (NmErased fc) = do Iconst 0; ret
    assembleExpr ret IDouble (NmErased fc) =  do Ldc $ DoubleConst 0; ret
    assembleExpr ret _ (NmErased fc) = do Aconstnull; ret
    assembleExpr ret exprTy (NmCrash fc msg) = do
        Ldc $ StringConst msg
        InvokeMethod InvokeStatic runtimeClass "crash" "(Ljava/lang/String;)Ljava/lang/Object;" False
        asmCast inferredObjectType exprTy
        ret
    assembleExpr _ _ expr = Throw (getFC expr) $ "Cannot compile " ++ show expr ++ " yet"

    assembleConstructorSwitchExpr : NamedCExp -> Asm Nat
    assembleConstructorSwitchExpr (NmLocal _ loc) = getVariableIndex $ jvmSimpleName loc
    assembleConstructorSwitchExpr sc = do
        idrisObjectVariableIndex <- getVariableIndex $ "constructorSwitchValue" ++ show !newDynamicVariableIndex
        assembleExpr (storeVar idrisObjectType idrisObjectType idrisObjectVariableIndex) idrisObjectType sc
        Pure idrisObjectVariableIndex

    assembleExprBinaryOp : Asm () -> InferredType -> InferredType -> Asm () -> NamedCExp -> NamedCExp -> Asm ()
    assembleExprBinaryOp ret returnType exprType operator expr1 expr2 =
        assembleExpr (assembleExpr ret1 exprType expr2) exprType expr1 where
            ret1 : Asm ()
            ret1 = do
                operator
                asmCast exprType returnType
                ret

    assembleExprBinaryBoolOp : Asm () -> InferredType -> InferredType -> (String -> Asm ()) ->
        NamedCExp -> NamedCExp -> Asm ()
    assembleExprBinaryBoolOp ret returnType exprType operator expr1 expr2 =
        assembleExpr (assembleExpr ret1 exprType expr2) exprType expr1
      where
        ret1 : Asm ()
        ret1 = do
            ifLabel <- newLabel
            CreateLabel ifLabel
            elseLabel <- newLabel
            CreateLabel elseLabel
            endLabel <- newLabel
            CreateLabel endLabel
            operator elseLabel
            LabelStart ifLabel
            scope <- getScope !getCurrentScopeIndex
            Iconst 1
            Goto endLabel
            LabelStart elseLabel
            Iconst 0
            LabelStart endLabel
            ret

    assembleExprComparableBinaryBoolOp : Asm () -> InferredType -> String -> (String -> Asm ()) ->
        NamedCExp -> NamedCExp -> Asm ()
    assembleExprComparableBinaryBoolOp ret returnType className operator expr1 expr2 =
        let exprType = IRef className
        in assembleExpr (assembleExpr ret1 exprType expr2) exprType expr1
      where
        ret1 : Asm ()
        ret1 = do
            ifLabel <- newLabel
            CreateLabel ifLabel
            elseLabel <- newLabel
            CreateLabel elseLabel
            endLabel <- newLabel
            CreateLabel endLabel
            InvokeMethod InvokeVirtual className "compareTo" ("(L" ++ className ++ ";)I") False
            operator elseLabel
            LabelStart ifLabel
            scope <- getScope !getCurrentScopeIndex
            Iconst 1
            Goto endLabel
            LabelStart elseLabel
            Iconst 0
            LabelStart endLabel
            ret

    assembleExprUnaryOp : (Asm ()) -> InferredType -> InferredType -> Asm () -> NamedCExp -> Asm ()
    assembleExprUnaryOp ret returnType exprType operator expr =  assembleExpr ret1 exprType expr where
        ret1 : Asm ()
        ret1 = do
            operator
            asmCast exprType returnType
            ret

    assembleStrCons : InferredType -> (char: NamedCExp) -> (str: NamedCExp) -> Asm ()
    assembleStrCons returnType char str = do
        New "java/lang/StringBuilder"
        Dup
        InvokeMethod InvokeSpecial "java/lang/StringBuilder" "<init>" "()V" False
        assembleExpr ret1 IChar char
      where
        ret2 : Asm ()
        ret2 = do
            InvokeMethod InvokeVirtual "java/lang/StringBuilder" "append"
                "(Ljava/lang/String;)Ljava/lang/StringBuilder;" False
            InvokeMethod InvokeVirtual "java/lang/StringBuilder" "toString" "()Ljava/lang/String;" False
            asmCast inferredStringType returnType

        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeVirtual "java/lang/StringBuilder" "append" "(C)Ljava/lang/StringBuilder;" False
            assembleExpr ret2 inferredStringType str

    assembleStrReverse : InferredType -> NamedCExp -> Asm ()
    assembleStrReverse returnType str = do
        New "java/lang/StringBuilder"
        Dup
        assembleExpr ret1 inferredStringType str
      where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeSpecial "java/lang/StringBuilder" "<init>" "(Ljava/lang/String;)V" False
            InvokeMethod InvokeVirtual "java/lang/StringBuilder" "reverse" "()Ljava/lang/StringBuilder;" False
            InvokeMethod InvokeVirtual "java/lang/StringBuilder" "toString" "()Ljava/lang/String;" False
            asmCast inferredStringType returnType

    assembleExprOp : Asm () -> InferredType -> FC -> PrimFn arity -> Vect arity NamedCExp -> Asm ()
    assembleExprOp ret returnType fc (Add IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Iadd x y
    assembleExprOp ret returnType fc (Sub IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Isub x y
    assembleExprOp ret returnType fc (Mul IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Imul x y
    assembleExprOp ret returnType fc (Div IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Idiv x y
    assembleExprOp ret returnType fc (Mod IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Irem x y
    assembleExprOp ret returnType fc (Neg IntType) [x] = assembleExprUnaryOp ret returnType IInt Ineg x
    assembleExprOp ret returnType fc (ShiftL IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Ishl x y
    assembleExprOp ret returnType fc (ShiftR IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Ishr x y
    assembleExprOp ret returnType fc (BAnd IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Iand x y
    assembleExprOp ret returnType fc (BOr IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Ior x y
    assembleExprOp ret returnType fc (BXOr IntType) [x, y] = assembleExprBinaryOp ret returnType IInt Ixor x y

    assembleExprOp ret returnType fc (Add IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "add"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp ret returnType inferredBigIntegerType op x y
    assembleExprOp ret returnType fc (Sub IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "subtract"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp ret returnType inferredBigIntegerType op x y
    assembleExprOp ret returnType fc (Mul IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "multiply"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp ret returnType inferredBigIntegerType op x y
    assembleExprOp ret returnType fc (Div IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "divide"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp ret returnType inferredBigIntegerType op x y
    assembleExprOp ret returnType fc (Mod IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "remainder"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp ret returnType inferredBigIntegerType op x y
    assembleExprOp ret returnType fc (Neg IntegerType) [x] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "negate"
                "()Ljava/math/BigInteger;" False
        in assembleExprUnaryOp ret returnType inferredBigIntegerType op x

    assembleExprOp ret returnType fc (Add DoubleType) [x, y] = assembleExprBinaryOp ret returnType IDouble Dadd x y
    assembleExprOp ret returnType fc (Sub DoubleType) [x, y] = assembleExprBinaryOp ret returnType IDouble Dsub x y
    assembleExprOp ret returnType fc (Mul DoubleType) [x, y] = assembleExprBinaryOp ret returnType IDouble Dmul x y
    assembleExprOp ret returnType fc (Div DoubleType) [x, y] = assembleExprBinaryOp ret returnType IDouble Ddiv x y
    assembleExprOp ret returnType fc (Neg DoubleType) [x] = assembleExprUnaryOp ret returnType IDouble Dneg x

    assembleExprOp ret returnType fc (LT CharType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmpge x y
    assembleExprOp ret returnType fc (LTE CharType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmpgt x y
    assembleExprOp ret returnType fc (EQ CharType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmpne x y
    assembleExprOp ret returnType fc (GTE CharType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmplt x y
    assembleExprOp ret returnType fc (GT CharType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmple x y

    assembleExprOp ret returnType fc (LT IntType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmpge x y
    assembleExprOp ret returnType fc (LTE IntType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmpgt x y
    assembleExprOp ret returnType fc (EQ IntType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmpne x y
    assembleExprOp ret returnType fc (GTE IntType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmplt x y
    assembleExprOp ret returnType fc (GT IntType) [x, y] = assembleExprBinaryBoolOp ret returnType IInt Ificmple x y

    assembleExprOp ret returnType fc (LT DoubleType) [x, y] =
        assembleExprBinaryBoolOp ret returnType IDouble (\label => do Dcmpg; Ifge label) x y
    assembleExprOp ret returnType fc (LTE DoubleType) [x, y] =
        assembleExprBinaryBoolOp ret returnType IDouble (\label => do Dcmpg; Ifgt label) x y
    assembleExprOp ret returnType fc (EQ DoubleType) [x, y] =
        assembleExprBinaryBoolOp ret returnType IDouble (\label => do Dcmpl; Ifne label) x y
    assembleExprOp ret returnType fc (GTE DoubleType) [x, y] =
        assembleExprBinaryBoolOp ret returnType IDouble (\label => do Dcmpl; Iflt label) x y
    assembleExprOp ret returnType fc (GT DoubleType) [x, y] =
        assembleExprBinaryBoolOp ret returnType IDouble (\label => do Dcmpl; Ifle label) x y

    assembleExprOp ret returnType fc (LT IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType bigIntegerClass Ifge x y
    assembleExprOp ret returnType fc (LTE IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType bigIntegerClass Ifgt x y
    assembleExprOp ret returnType fc (EQ IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType bigIntegerClass Ifne x y
    assembleExprOp ret returnType fc (GTE IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType bigIntegerClass Iflt x y
    assembleExprOp ret returnType fc (GT IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType bigIntegerClass Ifle x y

    assembleExprOp ret returnType fc (LT StringType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType stringClass Ifge x y
    assembleExprOp ret returnType fc (LTE StringType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType stringClass Ifgt x y
    assembleExprOp ret returnType fc (EQ StringType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType stringClass Ifne x y
    assembleExprOp ret returnType fc (GTE StringType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType stringClass Iflt x y
    assembleExprOp ret returnType fc (GT StringType) [x, y] =
        assembleExprComparableBinaryBoolOp ret returnType stringClass Ifle x y

    assembleExprOp ret returnType fc StrLength [x] = assembleExpr ret1 inferredStringType x where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeVirtual "java/lang/String" "length" "()I" False
            asmCast IInt returnType
            ret

    assembleExprOp ret returnType fc StrHead [x] = assembleExpr ret1 inferredStringType x where
        ret1 : Asm ()
        ret1 = do
            Iconst 0
            InvokeMethod InvokeVirtual "java/lang/String" "charAt" "(I)C" False
            asmCast IChar returnType
            ret

    assembleExprOp ret returnType fc StrTail [x] = assembleExpr ret1 inferredStringType x where
        ret1 : Asm ()
        ret1 = do
            Iconst 1
            InvokeMethod InvokeVirtual "java/lang/String" "substring" "(I)Ljava/lang/String;" False
            asmCast inferredStringType returnType
            ret

    assembleExprOp ret returnType fc StrIndex [x, i] = assembleExpr ret1 inferredStringType x where
        ret2 : Asm ()
        ret2 = do
            InvokeMethod InvokeVirtual "java/lang/String" "charAt" "(I)C" False
            asmCast IChar returnType
            ret

        ret1 : Asm ()
        ret1 = assembleExpr ret2 IInt i

    assembleExprOp ret returnType fc StrCons [x, y] = do assembleStrCons returnType x y; ret
    assembleExprOp ret returnType fc StrAppend [x, y] =
        let op = InvokeMethod InvokeVirtual "java/lang/String" "concat" "(Ljava/lang/String;)Ljava/lang/String;" False
        in assembleExprBinaryOp ret returnType inferredStringType op x y
    assembleExprOp ret returnType fc StrReverse [x] = do assembleStrReverse returnType x; ret
    assembleExprOp ret returnType fc StrSubstr [offset, len, str] = assembleExpr ret1 IInt offset where
        ret3 : Asm ()
        ret3 = do
            InvokeMethod InvokeStatic (getRuntimeClass "Strings") "substring"
                "(IILjava/lang/String;)Ljava/lang/String;" False
            asmCast inferredStringType returnType
            ret

        ret2 : Asm ()
        ret2 = assembleExpr ret3 inferredStringType str

        ret1 : Asm ()
        ret1 = assembleExpr ret2 IInt len

    {-assembleExprOp ret returnType fc  is Euler's number, which approximates to: 2.718281828459045
    assembleExprOp ret returnType fc DoubleExp [x] = op "exp" [x] -- Base is `e`. Same as: `pow(e, x)`
    assembleExprOp ret returnType fc DoubleLog [x] = op "log" [x] -- Base is `e`.
    assembleExprOp ret returnType fc DoubleSin [x] = op "sin" [x]
    assembleExprOp ret returnType fc DoubleCos [x] = op "cos" [x]
    assembleExprOp ret returnType fc DoubleTan [x] = op "tan" [x]
    assembleExprOp ret returnType fc DoubleASin [x] = op "asin" [x]
    assembleExprOp ret returnType fc DoubleACos [x] = op "acos" [x]
    assembleExprOp ret returnType fc DoubleATan [x] = op "atan" [x]
    assembleExprOp ret returnType fc DoubleSqrt [x] = op "sqrt" [x]
    assembleExprOp ret returnType fc DoubleFloor [x] = op "floor" [x]
    assembleExprOp ret returnType fc DoubleCeiling [x] = op "ceiling" [x]-}

    assembleExprOp ret returnType fc (Cast IntType StringType) [x] = assembleExpr ret1 IInt x where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeStatic "java/lang/Integer" "toString" "(I)Ljava/lang/String;" False
            asmCast inferredStringType returnType
            ret

    assembleExprOp ret returnType fc (Cast IntegerType StringType) [x] =
        assembleExpr ret1 inferredBigIntegerType x where
            ret1 : Asm ()
            ret1 = do
                InvokeMethod InvokeVirtual "java/math/BigInteger" "toString" "()Ljava/lang/String;" False
                asmCast inferredBigIntegerType returnType
                ret

    assembleExprOp ret returnType fc (Cast DoubleType StringType) [x] = assembleExpr ret1 IDouble x where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeStatic "java/lang/Double" "toString" "(D)Ljava/lang/String;" False
            asmCast inferredStringType returnType
            ret

    assembleExprOp ret returnType fc (Cast CharType StringType) [x] = assembleExpr ret1 IChar x where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeStatic "java/lang/Character" "toString" "(I)Ljava/lang/String;" False
            asmCast inferredStringType returnType
            ret

    assembleExprOp ret returnType fc (Cast IntType IntegerType) [x] = assembleExpr ret1 IInt x where
        ret1 : Asm ()
        ret1 = do
            I2l
            InvokeMethod InvokeStatic "java/math/BigInteger" "valueOf" "(J)Ljava/math/BigInteger;" False
            asmCast inferredBigIntegerType returnType
            ret

    assembleExprOp ret returnType fc (Cast DoubleType IntegerType) [x] = assembleExpr ret1 IDouble x where
        ret1 : Asm ()
        ret1 = do
            D2i
            I2l
            InvokeMethod InvokeStatic "java/math/BigInteger" "valueOf" "(J)Ljava/math/BigInteger;" False
            asmCast inferredBigIntegerType returnType
            ret

    assembleExprOp ret returnType fc (Cast CharType IntegerType) [x] = assembleExpr ret1 IInt x where
        ret1 : Asm ()
        ret1 = do
            I2l
            InvokeMethod InvokeStatic "java/math/BigInteger" "valueOf" "(J)Ljava/math/BigInteger;" False
            asmCast inferredBigIntegerType returnType
            ret
    assembleExprOp ret returnType fc (Cast StringType IntegerType) [x] = do
        New "java/math/BigInteger"
        Dup
        assembleExpr ret1 inferredStringType x
      where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeSpecial "java/math/BigDecimal" "<init>" "(Ljava/lang/String;)V" False
            InvokeMethod InvokeVirtual "java/math/BigInteger" "toBigInteger" "()Ljava/math/BigInteger;" False
            asmCast inferredBigIntegerType returnType
            ret

    assembleExprOp ret returnType fc (Cast IntegerType IntType) [x] = assembleExpr ret1 inferredBigIntegerType x where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeVirtual "java/math/BigInteger" "intValue" "()I" False
            asmCast IInt returnType
            ret

    assembleExprOp ret returnType fc (Cast DoubleType IntType) [x] = assembleExpr ret1 IDouble x where
        ret1 : Asm ()
        ret1 = do
            D2i
            asmCast IInt returnType
            ret

    assembleExprOp ret returnType fc (Cast StringType IntType) [x] = assembleExpr ret1 inferredStringType x where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeStatic "java/lang/Double" "parseDouble" "(Ljava/lang/String;)D" False
            D2i
            asmCast IInt returnType
            ret

    assembleExprOp ret returnType fc (Cast CharType IntType) [x] =
        assembleExpr (do asmCast IInt returnType; ret) IChar x

    assembleExprOp ret returnType fc (Cast IntegerType DoubleType) [x] =
        assembleExpr ret1 inferredBigIntegerType x where
            ret1 : Asm ()
            ret1 = do
                InvokeMethod InvokeVirtual "java/math/BigInteger" "doubleValue" "()D" False
                asmCast IDouble returnType
                ret

    assembleExprOp ret returnType fc (Cast IntType DoubleType) [x] = assembleExpr ret1 IInt x where
        ret1 : Asm ()
        ret1 = do
            I2d
            asmCast IDouble returnType
            ret
    assembleExprOp ret returnType fc (Cast StringType DoubleType) [x] = assembleExpr ret1 inferredStringType x where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeStatic "java/lang/Double" "parseDouble" "(Ljava/lang/String;)D" False
            asmCast IDouble returnType
            ret

    assembleExprOp ret returnType fc (Cast IntType CharType) [x] = assembleExpr ret1 IInt x where
        ret1 : Asm ()
        ret1 = do
            I2c
            asmCast IChar returnType
            ret

    assembleExprOp ret returnType fc BelieveMe [_,_,x] = assembleExpr (do asmCast IUnknown returnType; ret) IUnknown x

    assembleExprOp ret returnType fc Crash [_, msg] =  assembleExpr ret1 inferredStringType msg where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeStatic runtimeClass "crash" "(Ljava/lang/String;)Ljava/lang/Object;" False
            asmCast inferredObjectType returnType
            ret

    assembleExprOp ret returnType fc op _ = Throw fc ("Unsupported operator " ++ show op)

    assembleParameter : (NamedCExp, InferredType) -> Asm ()
    assembleParameter (param, ty) = assembleExpr (Pure ()) ty param

    storeParameter : (Nat, NamedCExp, InferredType) -> Asm ()
    storeParameter (var, (NmLocal _ loc), ty) = do
        let valueVariableName = jvmSimpleName loc
        valueVariableIndex <- getVariableIndex valueVariableName
        if var == valueVariableIndex then Pure ()
        else do
            valueVariableType <- getVariableType valueVariableName
            loadVar !getVariableTypes valueVariableType ty valueVariableIndex
            storeVar ty ty var
    storeParameter (var, param, ty) = assembleExpr (storeVar ty ty var) ty param

    substituteVariableSubMethodBody : NamedCExp -> NamedCExp -> NamedCExp
    substituteVariableSubMethodBody variable (NmConCase fc sc alts def) = NmConCase fc variable alts def
    substituteVariableSubMethodBody variable (NmConstCase fc sc alts def) = NmConstCase fc variable alts def
    substituteVariableSubMethodBody _ expr = expr

    assembleSubMethodWithScope : Asm () -> InferredType -> (parameterValue: Maybe NamedCExp) ->
        (parameterName : Maybe Name) -> NamedCExp -> Asm ()
    assembleSubMethodWithScope ret returnType (Just value) (Just name) body = do
        parentScope <- getScope !getCurrentScopeIndex
        parameterValueVariableIndex <- newDynamicVariableIndex
        let parameterValueVariable = jvmSimpleName name ++ show parameterValueVariableIndex
        withScope $ assembleSubMethod returnType (Just (assembleValue parentScope parameterValueVariable))
            (Just $ UN parameterValueVariable) parentScope
            (substituteVariableSubMethodBody (NmLocal (getFC body) $ UN parameterValueVariable) body)
        ret
      where
          assembleValue : Scope -> String -> Asm ()
          assembleValue enclosingScope variableName = do
            lambdaScopeIndex <- getCurrentScopeIndex
            variableType <- getVariableType variableName
            updateCurrentScopeIndex (index enclosingScope)
            assembleExpr (Pure ()) variableType value
            updateCurrentScopeIndex lambdaScopeIndex

    assembleSubMethodWithScope ret returnType _ parameterName body = do
        parentScope <- getScope !getCurrentScopeIndex
        withScope $ assembleSubMethod returnType Nothing parameterName parentScope body
        ret

    assembleSubMethod : InferredType -> (parameterValueExpr: (Maybe (Asm ()))) ->
        (parameterName: Maybe Name) -> Scope -> NamedCExp -> Asm ()
    assembleSubMethod lambdaReturnType parameterValueExpr parameterName declaringScope expr = do
            scope <- getScope !getCurrentScopeIndex
            maybe (Pure ()) (setScopeCounter . succ) (parentIndex scope)
            let lambdaBodyReturnType = returnType scope
            let lambdaType = getLambdaType parameterName
            let lambdaInterfaceType = getLambdaInterfaceType lambdaType lambdaBodyReturnType
            className <- getClassName
            parameterTypes <- traverse getVariableType
                (jvmSimpleName <$> (if parameterName == Just (UN "$jvm$thunk") then Nothing else parameterName))
            let variableTypes = SortedMap.values !(loadClosures declaringScope scope)
            maybe (Pure ()) id parameterValueExpr
            let invokeDynamicDescriptor = getMethodDescriptor $ MkInferredFunctionType lambdaInterfaceType variableTypes
            let implementationMethodReturnType = getLambdaImplementationMethodReturnType lambdaType
            let implementationMethodDescriptor = getMethodDescriptor $
                MkInferredFunctionType implementationMethodReturnType (variableTypes ++ toList parameterTypes)
            let instantiatedMethodDescriptor = getMethodDescriptor $
                MkInferredFunctionType implementationMethodReturnType $ toList parameterTypes
            let isExtracted = isJust parameterValueExpr
            let methodPrefix = if isExtracted then "extracted" else "lambda"
            lambdaMethodName <- getLambdaImplementationMethodName methodPrefix
            let interfaceMethodName = getLambdaInterfaceMethodName lambdaType
            let indy = do
                invokeDynamic className lambdaMethodName interfaceMethodName invokeDynamicDescriptor
                    (getSamDesc lambdaType) implementationMethodDescriptor instantiatedMethodDescriptor
                when (lambdaReturnType /= inferredObjectType) $ asmCast lambdaInterfaceType lambdaReturnType
            let staticCall = do
                 InvokeMethod InvokeStatic className lambdaMethodName implementationMethodDescriptor False
                 asmCast lambdaBodyReturnType lambdaReturnType
            maybe indy (const staticCall) parameterValueExpr

            let oldLineNumberLabels = lineNumberLabels !GetState
            updateState $ record { lineNumberLabels = SortedMap.empty }
            let accessModifiers = if isExtracted then [Private, Static]
                else [Private, Static, Synthetic]
            CreateMethod accessModifiers "" className lambdaMethodName implementationMethodDescriptor
                Nothing Nothing [] []
            MethodCodeStart
            let labelStart = methodStartLabel
            let labelEnd = methodEndLabel
            addLambdaStartLabel scope labelStart
            maybe (Pure ()) (\parentScopeIndex => updateScopeStartLabel parentScopeIndex labelStart) (parentIndex scope)
            let ret = if isExtracted then asmReturn lambdaBodyReturnType else castReturn lambdaType lambdaBodyReturnType
            when isExtracted $ Debug $ "extracted expr " ++ showNamedCExp 0 expr
            assembleExpr ret lambdaBodyReturnType expr
            addLambdaEndLabel scope labelEnd
            maybe (Pure ()) (\parentScopeIndex => updateScopeEndLabel parentScopeIndex labelEnd) (parentIndex scope)
            addLocalVariables $ fromMaybe (index scope) (parentIndex scope)
            MaxStackAndLocal (-1) (-1)
            MethodCodeEnd
            updateState $ record { lineNumberLabels = oldLineNumberLabels }
        where
            addLambdaStartLabel : Scope -> String -> Asm ()
            addLambdaStartLabel scope label = do
                let scopeIndex = index scope
                lambdaScope <- getScope scopeIndex
                let lineNumberStart = fst $ lineNumbers lambdaScope
                CreateLabel label
                LabelStart label
                addLineNumber lineNumberStart label
                updateScopeStartLabel scopeIndex label

            addLambdaEndLabel : Scope -> String -> Asm ()
            addLambdaEndLabel scope label = do
                let scopeIndex = index scope
                lambdaScope <- getScope scopeIndex
                let lineNumberEnd = snd $ lineNumbers lambdaScope
                CreateLabel label
                LabelStart label
                updateScopeEndLabel scopeIndex label

            castReturn : LambdaType -> InferredType -> Asm ()
            castReturn ThunkLambda returnType =
                if isThunkType returnType then asmReturn returnType
                else do
                    asmCast returnType thunkType
                    asmReturn thunkType
            castReturn _ returnType = do asmCast returnType inferredObjectType; asmReturn inferredObjectType

            loadVariables : SortedMap Nat InferredType -> SortedMap Nat (InferredType, InferredType) -> List Nat -> Asm ()
            loadVariables _ _ [] = Pure ()
            loadVariables declaringScopeVariableTypes types (var :: vars) = do
                let (sourceType, targetType) = fromMaybe (IUnknown, IUnknown) (SortedMap.lookup var types)
                loadVar declaringScopeVariableTypes sourceType targetType var
                loadVariables declaringScopeVariableTypes types vars

            loadClosures : Scope -> Scope -> Asm (SortedMap Nat InferredType)
            loadClosures declaringScope currentScope = case parentIndex currentScope of
                    Just parentScopeIndex => do
                        parentScope <- getScope parentScopeIndex
                        let variableNames = SortedMap.keys $ variableIndices parentScope
                        variableNameAndIndex <- traverse getVariableNameAndIndex variableNames
                        typesByIndex <- getIndexAndType SortedMap.empty variableNameAndIndex
                        declaringScopeVariableTypes <- getVariableTypesAtScope (index declaringScope)
                        loadVariables declaringScopeVariableTypes typesByIndex $ fst <$> SortedMap.toList typesByIndex
                        Pure $ SortedMap.fromList (getTargetType <$> SortedMap.toList typesByIndex)
                    Nothing => Pure SortedMap.empty
                where
                    getTargetType : (Nat, InferredType, InferredType) -> (Nat, InferredType)
                    getTargetType (varIndex, _, targetType) = (varIndex, targetType)

                    getVariableNameAndIndex : String -> Asm (String, Nat)
                    getVariableNameAndIndex name = do
                        variableIndex <- getVariableIndexAtScope (index declaringScope) name
                        Pure (name, variableIndex)

                    getIndexAndType : SortedMap Nat (InferredType, InferredType) -> List (String, Nat) ->
                        Asm (SortedMap Nat (InferredType, InferredType))
                    getIndexAndType acc [] = Pure acc
                    getIndexAndType acc ((name, varIndex) :: rest) = do
                        targetType <- getVariableType name
                        sourceType <- getVariableTypeAtScope (index declaringScope) name
                        getIndexAndType (SortedMap.insert varIndex (sourceType, targetType) acc) rest

    assembleMissingDefault : Asm () -> InferredType -> FC -> String -> Asm ()
    assembleMissingDefault ret returnType fc defaultLabel = do
        LabelStart defaultLabel
        assembleExpr ret returnType (NmCrash fc "Unreachable code")

    assembleConstantSwitch : Asm () -> (returnType: InferredType) -> (switchExprType: InferredType) -> FC ->
        NamedCExp -> List NamedConstAlt -> Maybe NamedCExp -> Asm ()
    assembleConstantSwitch _ _ _ fc _ [] _ = Throw fc "Empty cases"

    assembleConstantSwitch ret returnType IInt fc sc alts def = assembleExpr ret1 IInt sc where

        getCasesWithLabels : List NamedConstAlt -> Asm (List (String, Int, NamedConstAlt))
        getCasesWithLabels alts = do
            caseExpressionsWithLabels <- traverse (constantAltIntExpr fc) alts
            Pure $ sortBy (comparing second) caseExpressionsWithLabels

        assembleCaseWithScope : String -> String -> NamedCExp -> Asm ()
        assembleCaseWithScope labelStart labelEnd expr = withScope $ do
            scopeIndex <- getCurrentScopeIndex
            scope <- getScope scopeIndex
            let (lineNumberStart, lineNumberEnd) = lineNumbers scope
            LabelStart labelStart
            updateScopeStartLabel scopeIndex labelStart
            addLineNumber lineNumberStart labelStart
            updateScopeEndLabel scopeIndex labelEnd
            assembleExpr ret returnType expr

        assembleDefault : String -> NamedCExp -> Asm ()
        assembleDefault defaultLabel expr =  assembleCaseWithScope defaultLabel methodEndLabel expr

        assembleExprConstAlt : (String, Int, NamedConstAlt, String) -> Asm ()
        assembleExprConstAlt (labelStart, _, (MkNConstAlt _ expr), labelEnd) =
            assembleCaseWithScope labelStart labelEnd expr

        ret1 : Asm ()
        ret1 = do
            switchCases <- getCasesWithLabels alts
            let labels = fst <$> switchCases
            let exprs = second <$> switchCases
            traverse_ CreateLabel labels
            defaultLabel <- createDefaultLabel
            LookupSwitch defaultLabel labels exprs
            let switchCasesWithEndLabel = getSwitchCasesWithEndLabel switchCases labels
            traverse_ assembleExprConstAlt switchCasesWithEndLabel
            maybe (assembleMissingDefault ret returnType fc defaultLabel) (assembleDefault defaultLabel) def

    assembleConstantSwitch ret returnType constantType fc sc alts def = do
            constantExprVariableSuffixIndex <- newDynamicVariableIndex
            let constantExprVariableName = "constantCaseExpr" ++ show constantExprVariableSuffixIndex
            constantExprVariableIndex <- getVariableIndex constantExprVariableName
            hashCodePositionVariableSuffixIndex <- newDynamicVariableIndex
            let hashCodePositionVariableName = "hashCodePosition" ++ show hashCodePositionVariableSuffixIndex
            hashCodePositionVariableIndex <- getVariableIndex hashCodePositionVariableName
            hashPositionAndAlts <- traverse (constantAltHashCodeExpr fc) $ List.zip [0 .. length $ drop 1 alts] alts
            let positionAndAltsByHash = multiValueMap fst snd hashPositionAndAlts
            hashCodeSwitchCases <- getHashCodeCasesWithLabels positionAndAltsByHash
            let labels = fst <$> hashCodeSwitchCases
            let exprs = second <$> hashCodeSwitchCases
            switchEndLabel <- newLabel
            CreateLabel switchEndLabel
            traverse_ CreateLabel labels
            assembleExpr (storeVar constantType constantType constantExprVariableIndex) constantType sc
            constantClass <- getHashCodeSwitchClass fc constantType
            Iconst (-1)
            storeVar IInt IInt hashCodePositionVariableIndex
            loadVar !getVariableTypes constantType constantType constantExprVariableIndex
            InvokeMethod InvokeVirtual constantClass "hashCode" "()I" False
            LookupSwitch switchEndLabel labels exprs
            traverse_
                (assembleHashCodeSwitchCases fc constantClass constantExprVariableIndex hashCodePositionVariableIndex
                    switchEndLabel)
                hashCodeSwitchCases
            scope <- getScope !getCurrentScopeIndex
            let lineNumberStart = fst $ lineNumbers scope
            LabelStart switchEndLabel
            addLineNumber lineNumberStart switchEndLabel
            assembleConstantSwitch ret returnType IInt fc (NmLocal fc $ UN hashCodePositionVariableName)
                (hashPositionSwitchAlts hashPositionAndAlts) def
        where
            constantAltHashCodeExpr : FC -> (Nat, NamedConstAlt) -> Asm (Int, Nat, NamedConstAlt)
            constantAltHashCodeExpr fc positionAndAlt@(position, MkNConstAlt constant _) = do
                Just hashCodeValue <- hashCode constant
                    | Nothing => Throw fc ("Constant " ++ show constant ++ " cannot be compiled to 'Switch'.")
                Pure (hashCodeValue, position, snd positionAndAlt)

            hashPositionSwitchAlts : List (Int, Nat, NamedConstAlt) -> List NamedConstAlt
            hashPositionSwitchAlts exprPositionAlts = reverse $ go [] exprPositionAlts where
                go : List NamedConstAlt -> List (Int, Nat, NamedConstAlt) -> List NamedConstAlt
                go acc [] = acc
                go acc ((_, position, (MkNConstAlt _ expr)) :: alts) =
                    go (MkNConstAlt (I $ cast position) expr :: acc) alts

            assembleHashCodeSwitchCases : FC -> String -> Nat -> Nat -> String ->
                (String, Int, List (Nat, NamedConstAlt)) -> Asm ()
            assembleHashCodeSwitchCases fc _ _ _ _ (_, _, []) = Throw fc "Empty cases"
            assembleHashCodeSwitchCases fc constantClass constantExprVariableIndex hashCodePositionVariableIndex
                switchEndLabel (label, _, positionAndAlts) = go label positionAndAlts where
                    go : String -> List (Nat, NamedConstAlt) -> Asm ()
                    go _ [] = Pure ()
                    go label (positionAndAlt :: nextPositionAndAlt :: positionAndAlts) = do
                        let (position, (MkNConstAlt constant _)) = positionAndAlt
                        scope <- getScope !getCurrentScopeIndex
                        let lineNumberStart = fst $ lineNumbers scope
                        LabelStart switchEndLabel
                        addLineNumber lineNumberStart switchEndLabel
                        LabelStart label
                        addLineNumber lineNumberStart label
                        loadVar !getVariableTypes constantType constantType constantExprVariableIndex
                        assembleHashCodeSwitchConstant fc constant
                        InvokeMethod InvokeVirtual constantClass "equals" "(Ljava/lang/Object;)Z" False
                        nextLabel <- newLabel
                        Ifeq nextLabel
                        Iconst $ cast position
                        storeVar IInt IInt hashCodePositionVariableIndex
                        Goto switchEndLabel
                        go nextLabel (nextPositionAndAlt :: positionAndAlts)
                    go label (positionAndAlt :: []) = do
                        let (position, (MkNConstAlt constant _)) = positionAndAlt
                        scope <- getScope !getCurrentScopeIndex
                        let lineNumberStart = fst $ lineNumbers scope
                        LabelStart label
                        addLineNumber lineNumberStart label
                        loadVar !getVariableTypes constantType constantType constantExprVariableIndex
                        assembleHashCodeSwitchConstant fc constant
                        InvokeMethod InvokeVirtual constantClass "equals" "(Ljava/lang/Object;)Z" False
                        Ifeq switchEndLabel
                        Iconst $ cast position
                        storeVar IInt IInt hashCodePositionVariableIndex
                        Goto switchEndLabel

    assembleConCaseExpr : Asm () -> InferredType -> Nat -> Name -> List Name -> NamedCExp -> Asm ()
    assembleConCaseExpr ret returnType idrisObjectVariableIndex name args expr = do
            bindArg 0 args
            assembleExpr ret returnType expr
        where
            constructorType : InferredType
            constructorType = IRef $ jvmSimpleName name

            bindArg : Nat -> List Name -> Asm ()
            bindArg _ [] = Pure ()
            bindArg index (var :: vars) = do
                let variableName = jvmSimpleName var
                when (used variableName expr) $ do
                    loadVar !getVariableTypes idrisObjectType idrisObjectType idrisObjectVariableIndex
                    Iconst $ cast index
                    InvokeMethod InvokeInterface idrisObjectClass "getProperty" "(I)Ljava/lang/Object;" True
                    variableIndex <- getVariableIndex variableName
                    storeVar inferredObjectType !(getVariableType variableName) variableIndex
                bindArg (index + 1) vars

    assembleConstructorSwitch : Asm () -> InferredType -> FC -> Nat -> List NamedConAlt ->
        Maybe NamedCExp -> Asm ()
    assembleConstructorSwitch ret returnType fc idrisObjectVariableIndex alts def = do
            switchCases <- getCasesWithLabels alts
            let labels = fst <$> switchCases
            let switchCasesWithEndLabel = getSwitchCasesWithEndLabel switchCases labels
            let exprs = caseExpression <$> switchCases
            traverse_ CreateLabel labels
            defaultLabel <- createDefaultLabel
            LookupSwitch defaultLabel labels exprs
            traverse_ assembleExprConAlt switchCasesWithEndLabel
            maybe (assembleMissingDefault ret returnType fc defaultLabel) (assembleDefault defaultLabel) def
        where
            caseExpression : (String, Int, NamedConAlt) -> Int
            caseExpression (_, expr, _) = expr

            getCasesWithLabels : List NamedConAlt -> Asm (List (String, Int, NamedConAlt))
            getCasesWithLabels alts = do
                caseExpressionsWithLabels <- traverse conAltIntExpr alts
                Pure $ sortBy (comparing caseExpression) caseExpressionsWithLabels

            assembleDefault : String -> NamedCExp -> Asm ()
            assembleDefault labelStart expr = withScope $ do
                scopeIndex <- getCurrentScopeIndex
                scope <- getScope scopeIndex
                let (lineNumberStart, lineNumberEnd) = lineNumbers scope
                LabelStart labelStart
                addLineNumber lineNumberStart labelStart
                updateScopeStartLabel scopeIndex labelStart
                updateScopeEndLabel scopeIndex methodEndLabel
                assembleExpr ret returnType expr

            assembleCaseWithScope : String -> String -> Name -> List Name -> NamedCExp -> Asm ()
            assembleCaseWithScope labelStart labelEnd name args expr = withScope $ do
                scopeIndex <- getCurrentScopeIndex
                scope <- getScope scopeIndex
                let (lineNumberStart, lineNumberEnd) = lineNumbers scope
                LabelStart labelStart
                addLineNumber lineNumberStart labelStart
                updateScopeStartLabel scopeIndex labelStart
                updateScopeEndLabel scopeIndex labelEnd
                assembleConCaseExpr ret returnType idrisObjectVariableIndex name args expr

            assembleExprConAlt : (String, Int, NamedConAlt, String) -> Asm ()
            assembleExprConAlt (labelStart, _, (MkNConAlt name tag args expr), labelEnd) =
                assembleCaseWithScope labelStart labelEnd name args expr

        assembleStringConstructorSwitch : Asm () -> InferredType -> FC -> Nat -> List NamedConAlt ->
                Maybe NamedCExp -> Asm ()
        assembleStringConstructorSwitch ret returnType fc idrisObjectVariableIndex alts def = do
            constantExprVariableSuffixIndex <- newDynamicVariableIndex
            let constantExprVariableName = "constructorCaseExpr" ++ show constantExprVariableSuffixIndex
            constantExprVariableIndex <- getVariableIndex constantExprVariableName
            storeVar inferredStringType inferredStringType constantExprVariableIndex
            hashCodePositionVariableSuffixIndex <- newDynamicVariableIndex
            let hashCodePositionVariableName = "hashCodePosition" ++ show hashCodePositionVariableSuffixIndex
            hashCodePositionVariableIndex <- getVariableIndex hashCodePositionVariableName
            hashPositionAndAlts <- traverse (conAltHashCodeExpr fc) $ List.zip [0 .. length $ drop 1 alts] alts
            let positionAndAltsByHash = multiValueMap fst snd hashPositionAndAlts
            hashCodeSwitchCases <- getHashCodeCasesWithLabels positionAndAltsByHash
            let labels = fst <$> hashCodeSwitchCases
            let exprs = second <$> hashCodeSwitchCases
            switchEndLabel <- newLabel
            CreateLabel switchEndLabel
            traverse_ CreateLabel labels
            let constantType = inferredStringType
            constantClass <- getHashCodeSwitchClass fc constantType
            Iconst (-1)
            storeVar IInt IInt hashCodePositionVariableIndex
            loadVar !getVariableTypes constantType constantType constantExprVariableIndex
            InvokeMethod InvokeVirtual constantClass "hashCode" "()I" False
            LookupSwitch switchEndLabel labels exprs
            traverse_
                (assembleHashCodeSwitchCases fc constantClass constantExprVariableIndex hashCodePositionVariableIndex
                    switchEndLabel)
                hashCodeSwitchCases
            scope <- getScope !getCurrentScopeIndex
            let lineNumberStart = fst $ lineNumbers scope
            LabelStart switchEndLabel
            addLineNumber lineNumberStart switchEndLabel
            assembleExpr (Pure ()) IInt (NmLocal fc $ UN hashCodePositionVariableName)
            assembleConstructorSwitch ret returnType fc idrisObjectVariableIndex
                (hashPositionSwitchAlts hashPositionAndAlts) def
        where
            conAltHashCodeExpr : FC -> (Nat, NamedConAlt) -> Asm (Int, Nat, NamedConAlt)
            conAltHashCodeExpr fc positionAndAlt@(position, MkNConAlt name _ _ _) = do
                Just hashCodeValue <- hashCode (Str $ jvmSimpleName name)
                    | Nothing => Throw fc ("Constructor " ++ show name ++ " cannot be compiled to 'Switch'.")
                Pure (hashCodeValue, position, snd positionAndAlt)

            hashPositionSwitchAlts : List (Int, Nat, NamedConAlt) -> List NamedConAlt
            hashPositionSwitchAlts exprPositionAlts = reverse $ go [] exprPositionAlts where
                go : List NamedConAlt -> List (Int, Nat, NamedConAlt) -> List NamedConAlt
                go acc [] = acc
                go acc ((_, position, (MkNConAlt name _ args expr)) :: alts) =
                    go (MkNConAlt name (Just $ cast position) args expr :: acc) alts

            assembleHashCodeSwitchCases : FC -> String -> Nat -> Nat -> String ->
                (String, Int, List (Nat, NamedConAlt)) -> Asm ()
            assembleHashCodeSwitchCases fc _ _ _ _ (_, _, []) = Throw fc "Empty cases"
            assembleHashCodeSwitchCases fc constantClass constantExprVariableIndex hashCodePositionVariableIndex
                switchEndLabel (label, _, positionAndAlts) = go label positionAndAlts where
                    go : String -> List (Nat, NamedConAlt) -> Asm ()
                    go _ [] = Pure ()
                    go label (positionAndAlt :: nextPositionAndAlt :: positionAndAlts) = do
                        let (position, (MkNConAlt name _ _ _)) = positionAndAlt
                        scope <- getScope !getCurrentScopeIndex
                        let lineNumberStart = fst $ lineNumbers scope
                        LabelStart switchEndLabel
                        addLineNumber lineNumberStart switchEndLabel
                        LabelStart label
                        addLineNumber lineNumberStart label
                        loadVar !getVariableTypes inferredStringType inferredStringType constantExprVariableIndex
                        Ldc $ StringConst $ jvmSimpleName name
                        InvokeMethod InvokeVirtual constantClass "equals" "(Ljava/lang/Object;)Z" False
                        nextLabel <- newLabel
                        Ifeq nextLabel
                        Iconst $ cast position
                        storeVar IInt IInt hashCodePositionVariableIndex
                        Goto switchEndLabel
                        go nextLabel (nextPositionAndAlt :: positionAndAlts)
                    go label (positionAndAlt :: []) = do
                        let (position, (MkNConAlt name _ _ _)) = positionAndAlt
                        scope <- getScope !getCurrentScopeIndex
                        let lineNumberStart = fst $ lineNumbers scope
                        LabelStart label
                        addLineNumber lineNumberStart label
                        loadVar !getVariableTypes inferredStringType inferredStringType constantExprVariableIndex
                        Ldc $ StringConst $ jvmSimpleName name
                        InvokeMethod InvokeVirtual constantClass "equals" "(Ljava/lang/Object;)Z" False
                        Ifeq switchEndLabel
                        Iconst $ cast position
                        storeVar IInt IInt hashCodePositionVariableIndex
                        Goto switchEndLabel

    jvmExtPrim : Asm () -> InferredType -> ExtPrim -> List NamedCExp -> Asm ()
    jvmExtPrim returns returnType JvmStaticMethodCall [ret, NmPrimVal fc (Str fn), fargs, world] = do
        args <- getFArgs fargs
        argTypes <- traverse tySpec (map fst args)
        methodReturnType <- tySpec ret
        traverse assembleParameter $ List.zip (map snd args) argTypes
        let methodDescriptor = getMethodDescriptor $ MkInferredFunctionType methodReturnType argTypes
        let (cname, mnameWithDot) = break (== '.') fn
        let (_, mname) = break (/= '.') mnameWithDot
        InvokeMethod InvokeStatic cname mname methodDescriptor False
        asmCast methodReturnType returnType
        returns
    jvmExtPrim ret returnType NewArray [_, size, val, world] = assembleExpr ret1 IInt size where
        ret2 : Asm ()
        ret2 = do
            InvokeMethod InvokeStatic arraysClass "create" "(ILjava/lang/Object;)Ljava/util/ArrayList;" False
            asmCast arrayListType returnType
            ret

        ret1 : Asm ()
        ret1 = assembleExpr ret2 IUnknown val
    jvmExtPrim ret returnType ArrayGet [_, arr, pos, world] = assembleExpr ret1 arrayListType arr where
        ret2 : Asm ()
        ret2 = do
            InvokeMethod InvokeVirtual arrayListClass "get" "(I)Ljava/lang/Object;" False
            asmCast inferredObjectType returnType
            ret

        ret1 : Asm ()
        ret1 = assembleExpr ret2 IInt pos
    jvmExtPrim ret returnType ArraySet [_, arr, pos, val, world] = assembleExpr ret1 arrayListType arr where
        ret3 : Asm ()
        ret3 = do
            InvokeMethod InvokeVirtual arrayListClass "set" "(ILjava/lang/Object;)Ljava/lang/Object;" False
            ret

        ret2 : Asm ()
        ret2 = assembleExpr ret3 IUnknown val

        ret1 : Asm ()
        ret1 = assembleExpr ret2 IInt pos
    jvmExtPrim _ _ prim args = Throw emptyFC ("Unsupported external function " ++ show prim)

assembleDefinition : {auto c : Ref Ctxt Defs} -> Name -> FC -> NamedDef -> Asm ()
assembleDefinition idrisName fc def@(MkNmFun args expr) = do
    let jname = jvmName idrisName
    resetScope
    loadFunction jname
    functionType <- getFunctionType jname
    function <- getFunction jname
    let jvmClassAndMethodName = jvmClassMethodName function
    let declaringClassName = className jvmClassAndMethodName
    let methodName = methodName jvmClassAndMethodName
    let methodReturnType = returnType functionType
    let descriptor = getMethodDescriptor functionType
    let fileName = fst $ getSourceLocationFromFc fc
    updateState $ record {
        scopeCounter = 0,
        currentScopeIndex = 0,
        lambdaCounter = 0,
        labelCounter = 1,
        lineNumberLabels = SortedMap.empty }
    updateCurrentFunction $ record { dynamicVariableCounter = 0 }
    let optimizedExpr = optimizedBody function
    Debug $ "************* " ++ show jname ++ ", " ++ show idrisName ++ "(" ++ show args ++ ")" ++ "*******"
    Debug $ showNamedCExp 0 optimizedExpr
    CreateMethod [Public, Static] fileName declaringClassName methodName descriptor Nothing Nothing [] []
    MethodCodeStart
    CreateLabel methodStartLabel
    CreateLabel methodEndLabel
    LabelStart methodStartLabel
    withScope $ do
        scopeIndex <- getCurrentScopeIndex
        scope <- getScope scopeIndex
        let (lineNumberStart, lineNumberEnd) = lineNumbers scope
        addLineNumber lineNumberStart methodStartLabel
        updateScopeStartLabel scopeIndex methodStartLabel
        updateScopeEndLabel scopeIndex methodEndLabel
        assembleExpr (asmReturn methodReturnType) methodReturnType optimizedExpr
        LabelStart methodEndLabel
    addLocalVariables 0
    MaxStackAndLocal (-1) (-1)
    MethodCodeEnd

assembleDefinition idrisName fc (MkNmError expr) = assembleDefinition idrisName fc (MkNmFun [] expr)
assembleDefinition idrisName fc def@(MkNmForeign _ argumentTypes _) = do
    let jname = jvmName idrisName
    function <- getFunction jname
    let arity = length argumentTypes
    let args =
       if arity > 0 then (\argumentIndex => UN $ "arg" ++ show argumentIndex) <$> [0 .. Nat.pred arity] else []
    assembleDefinition idrisName fc (MkNmFun args $ optimizedBody function)
assembleDefinition idrisName fc def@(MkNmCon t a _) = Pure ()

createMainMethod : Asm ()
createMainMethod = do
    CreateMethod [Public, Static] "Main.idr" "Main" "main" "([Ljava/lang/String;)V" Nothing Nothing [] []
    MethodCodeStart
    Aload 0
    InvokeMethod InvokeStatic runtimeClass "setProgramArgs" "([Ljava/lang/String;)V" False
    function <- getFunction $ jvmName idrisMainFunctionName
    let idrisMainClassMethodName = jvmClassMethodName function
    let methodType = inferredFunctionType function
    let methodDescriptor = getMethodDescriptor methodType
    InvokeMethod InvokeStatic (className idrisMainClassMethodName) (methodName idrisMainClassMethodName)
        methodDescriptor False
    when (isThunkType $ returnType methodType) unwrapObjectThunk
    Return
    MaxStackAndLocal (-1) (-1)
    MethodCodeEnd

asm : AsmState -> Asm a -> Core (a, AsmState)
asm = if shouldDebug then mockRunAsm else runAsm

lookupAndInfer : SortedMap Name (FC, NamedDef) -> Name -> Asm ()
lookupAndInfer fcAndDefinitionsByName name = case SortedMap.lookup name fcAndDefinitionsByName of
    Just (fc, def) => inferDef name fc def
    Nothing => Pure ()

lookupAndAssemble : {auto c : Ref Ctxt Defs} -> SortedMap Name (FC, NamedDef) -> Name -> Asm ()
lookupAndAssemble fcAndDefinitionsByName name = case SortedMap.lookup name fcAndDefinitionsByName of
    Just (fc, def) => assembleDefinition name fc def
    Nothing => Pure ()

||| Compile a TT expression to JVM bytecode
compileToJvmBytecode : Ref Ctxt Defs -> String -> ClosedTerm -> Core ()
compileToJvmBytecode c outputDirectory tm = do
    cdata <- getCompileData Cases tm
    let ndefs = namedDefs cdata
    let idrisMainBody = forget (mainExpr cdata)
    asmState <- newAsmState
    let fcAndDefinitionsByName = SortedMap.fromList $
        ((idrisMainFunctionName, (emptyFC, MkNmFun [] idrisMainBody)) ::
            map (\(name, fc, def) => (name, fc, def)) ndefs)
    let definitionsByName = SortedMap.fromList
        ((\(name, fc, def) => (name, def)) <$> SortedMap.toList fcAndDefinitionsByName)
    let orderedFunctions = traverseDepthFirst $ buildFunctionTreeMain $ definitionsByName
    _ <- asm asmState $ do
        traverse (lookupAndInfer fcAndDefinitionsByName) orderedFunctions
        traverse_ (lookupAndAssemble fcAndDefinitionsByName) orderedFunctions
        createMainMethod
        ClassCodeEnd outputDirectory
    pure ()

||| JVM bytecode implementation of the `compileExpr` interface.
compileExprJvm : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> (outputFile : String) -> Core (Maybe String)
compileExprJvm c execDir tm outputFile
    = do let outputDirectory = if outputFile == "" then "" else execDir ++ dirSep ++ outputFile ++ "_app"
         when (outputDirectory /= "") $ do
            coreLift $ mkdirs (splitDir outputDirectory)
            pure ()
         compileToJvmBytecode c outputDirectory tm
         pure $ Just outputDirectory

||| JVM bytecode implementation of the `executeExpr` interface.
||| This implementation simply runs the usual compiler, saving it to a temp file, then interpreting it.
executeExprJvm : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExprJvm c execDir tm = do compileExprJvm c execDir tm ""; pure ()

||| Codegen wrapper for Chez scheme implementation.
export
codegenJvm : Codegen
codegenJvm = MkCG compileExprJvm executeExprJvm
