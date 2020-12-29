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

exitScope : Scope -> Asm ()
exitScope targetScope = updateCurrentScopeIndex $ index targetScope

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
    assembleExpr : (isTailCall: Bool) -> InferredType -> NamedCExp -> Asm ()
    assembleExpr isTailCall returnType (NmDelay _ expr) = 
        assembleSubMethodWithScope isTailCall returnType Nothing Nothing expr
    assembleExpr isTailCall returnType (NmLocal _ loc) = do
        let variableName = jvmSimpleName loc
        index <- getVariableIndex variableName
        variableType <- getVariableType variableName
        loadVar !getVariableTypes variableType returnType index
        when isTailCall $ asmReturn returnType

    assembleExpr isTailCall returnType (NmApp _ (NmLam _ var body) [argument]) =
        assembleSubMethodWithScope isTailCall returnType (Just argument) (Just var) body
    assembleExpr isTailCall returnType (NmLam _ parameter body) =
        assembleSubMethodWithScope isTailCall returnType Nothing (Just parameter) body

    assembleExpr isTailCall returnType (NmLet _ var value expr) = do
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
            assembleExpr False variableType value
            storeVar variableType variableType variableIndex

        withScope $ do
            targetExprScopeIndex <- getCurrentScopeIndex
            scope <- getScope targetExprScopeIndex
            let (lineNumberStart, lineNumberEnd) = lineNumbers scope
            updateScopeStartLabel targetExprScopeIndex targetExprScopeStartLabel
            LabelStart targetExprScopeStartLabel
            addLineNumber lineNumberStart targetExprScopeStartLabel
            updateScopeEndLabel targetExprScopeIndex methodEndLabel
            assembleExpr isTailCall returnType expr

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

    assembleExpr isTailCall returnType (NmApp _ (NmRef _ idrisName) args) = do
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
        when isTailCall $ asmReturn returnType

    assembleExpr isTailCall returnType (NmApp _ lambdaVariable [arg]) = do
        assembleExpr False inferredLambdaType lambdaVariable
        assembleExpr False inferredObjectType arg
        InvokeMethod InvokeInterface "java/util/function/Function" "apply"
            "(Ljava/lang/Object;)Ljava/lang/Object;" True
        asmCast inferredObjectType returnType
        when isTailCall $ asmReturn returnType

    assembleExpr isTailCall returnType expr@(NmCon fc name tag args) = do
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
        when isTailCall $ asmReturn returnType

    assembleExpr isTailCall returnType (NmOp fc fn args) = do
        assembleExprOp returnType fc fn args
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmExtPrim fc p args) = do
        jvmExtPrim returnType (toPrim p) args
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmForce _ expr) = do
        assembleExpr False delayedType expr
        InvokeMethod InvokeStatic runtimeClass "force" "(Ljava/lang/Object;)Ljava/lang/Object;" False
        asmCast inferredObjectType returnType
        when isTailCall $ asmReturn returnType

    assembleExpr isTailCall returnType (NmConCase fc sc [] Nothing) = do
        defaultValue returnType
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmConCase fc sc [] (Just expr)) = do
        assembleConstructorSwitchExpr sc
        assembleExpr isTailCall returnType expr
    assembleExpr isTailCall returnType (NmConCase fc sc [MkNConAlt name _ args expr] Nothing) = do
        idrisObjectVariableIndex <- assembleConstructorSwitchExpr sc
        assembleConCaseExpr returnType idrisObjectVariableIndex name args expr
    assembleExpr isTailCall returnType (NmConCase fc sc alts def) = do
        idrisObjectVariableIndex <- assembleConstructorSwitchExpr sc
        let hasTypeCase = any isTypeCase alts
        let constructorType = if hasTypeCase then "Ljava/lang/String;" else "I"
        loadVar !getVariableTypes idrisObjectType idrisObjectType idrisObjectVariableIndex
        let constructorGetter = if hasTypeCase then "getStringConstructorId" else "getConstructorId"
        InvokeMethod InvokeInterface idrisObjectClass constructorGetter ("()" ++ constructorType) True
        if hasTypeCase then
            assembleStringConstructorSwitch returnType fc idrisObjectVariableIndex alts def
        else assembleConstructorSwitch returnType fc idrisObjectVariableIndex alts def

    assembleExpr isTailCall returnType (NmConstCase fc sc [] Nothing) = do
        defaultValue returnType
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmConstCase fc sc [] (Just expr)) = assembleExpr isTailCall returnType expr
    assembleExpr isTailCall returnType (NmConstCase fc sc alts@(_ :: _) def) = do
        constantType <- getConstantType alts
        assembleConstantSwitch returnType constantType fc sc alts def

    assembleExpr isTailCall returnType (NmPrimVal fc (I value)) = do
        Iconst value
        asmCast IInt returnType
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmPrimVal fc (BI value)) = do
        loadBigInteger $ show value
        asmCast inferredBigIntegerType returnType
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmPrimVal fc (Str value)) = do
        Ldc $ StringConst value
        asmCast inferredStringType returnType
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmPrimVal fc (Ch value)) = do
        Iconst (cast value)
        asmCast IChar returnType
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmPrimVal fc (Db value)) = do
        Ldc $ DoubleConst value
        asmCast IDouble returnType
        when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmPrimVal fc WorldVal) = do Aconstnull; when isTailCall $ asmReturn returnType
    assembleExpr isTailCall IInt (NmErased fc) = do Iconst 0; when isTailCall $ asmReturn IInt
    assembleExpr isTailCall IChar (NmErased fc) = do Iconst 0; when isTailCall $ asmReturn IChar
    assembleExpr isTailCall IDouble (NmErased fc) =  do Ldc $ DoubleConst 0; when isTailCall $ asmReturn IDouble
    assembleExpr isTailCall returnType (NmErased fc) = do Aconstnull; when isTailCall $ asmReturn returnType
    assembleExpr isTailCall returnType (NmCrash fc msg) = do
        Ldc $ StringConst msg
        InvokeMethod InvokeStatic runtimeClass "crash" "(Ljava/lang/String;)Ljava/lang/Object;" False
        asmCast inferredObjectType returnType
        when isTailCall $ asmReturn returnType
    assembleExpr _ _ expr = Throw (getFC expr) $ "Cannot compile " ++ show expr ++ " yet"

    assembleConstructorSwitchExpr : NamedCExp -> Asm Nat
    assembleConstructorSwitchExpr (NmLocal _ loc) = getVariableIndex $ jvmSimpleName loc
    assembleConstructorSwitchExpr sc = do
        idrisObjectVariableIndex <- getVariableIndex $ "constructorSwitchValue" ++ show !newDynamicVariableIndex
        assembleExpr False idrisObjectType sc
        storeVar idrisObjectType idrisObjectType idrisObjectVariableIndex
        Pure idrisObjectVariableIndex

    assembleExprBinaryOp : InferredType -> InferredType -> Asm () -> NamedCExp -> NamedCExp -> Asm ()
    assembleExprBinaryOp returnType exprType operator expr1 expr2 = do
        assembleExpr False exprType expr1
        assembleExpr False exprType expr2
        operator
        asmCast exprType returnType

    assembleExprBinaryBoolOp : InferredType -> InferredType -> (String -> Asm ()) ->
        NamedCExp -> NamedCExp -> Asm ()
    assembleExprBinaryBoolOp returnType exprType operator expr1 expr2 = do
        assembleExpr False exprType expr1
        assembleExpr False exprType expr2
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
        asmCast IInt returnType

    assembleExprComparableBinaryBoolOp : InferredType -> String -> (String -> Asm ()) ->
        NamedCExp -> NamedCExp -> Asm ()
    assembleExprComparableBinaryBoolOp returnType className operator expr1 expr2 = do
        let exprType = IRef className
        assembleExpr False exprType expr1
        assembleExpr False exprType expr2
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
        asmCast IInt returnType

    assembleExprUnaryOp : InferredType -> InferredType -> Asm () -> NamedCExp -> Asm ()
    assembleExprUnaryOp returnType exprType operator expr = do
        assembleExpr False exprType expr
        operator
        asmCast exprType returnType

    assembleStrCons : InferredType -> (char: NamedCExp) -> (str: NamedCExp) -> Asm ()
    assembleStrCons returnType char str = do
        New "java/lang/StringBuilder"
        Dup
        InvokeMethod InvokeSpecial "java/lang/StringBuilder" "<init>" "()V" False
        assembleExpr False IChar char
        InvokeMethod InvokeVirtual "java/lang/StringBuilder" "append" "(C)Ljava/lang/StringBuilder;" False
        assembleExpr False inferredStringType str
        InvokeMethod InvokeVirtual "java/lang/StringBuilder" "append"
            "(Ljava/lang/String;)Ljava/lang/StringBuilder;" False
        InvokeMethod InvokeVirtual "java/lang/StringBuilder" "toString" "()Ljava/lang/String;" False
        asmCast inferredStringType returnType

    assembleStrReverse : InferredType -> NamedCExp -> Asm ()
    assembleStrReverse returnType str = do
        New "java/lang/StringBuilder"
        Dup
        assembleExpr False inferredStringType str
        InvokeMethod InvokeSpecial "java/lang/StringBuilder" "<init>" "(Ljava/lang/String;)V" False
        InvokeMethod InvokeVirtual "java/lang/StringBuilder" "reverse" "()Ljava/lang/StringBuilder;" False
        InvokeMethod InvokeVirtual "java/lang/StringBuilder" "toString" "()Ljava/lang/String;" False
        asmCast inferredStringType returnType

    assembleExprOp : InferredType -> FC -> PrimFn arity -> Vect arity NamedCExp -> Asm ()
    assembleExprOp returnType fc (Add IntType) [x, y] = assembleExprBinaryOp returnType IInt Iadd x y
    assembleExprOp returnType fc (Sub IntType) [x, y] = assembleExprBinaryOp returnType IInt Isub x y
    assembleExprOp returnType fc (Mul IntType) [x, y] = assembleExprBinaryOp returnType IInt Imul x y
    assembleExprOp returnType fc (Div IntType) [x, y] = assembleExprBinaryOp returnType IInt Idiv x y
    assembleExprOp returnType fc (Mod IntType) [x, y] = assembleExprBinaryOp returnType IInt Irem x y
    assembleExprOp returnType fc (Neg IntType) [x] = assembleExprUnaryOp returnType IInt Ineg x
    assembleExprOp returnType fc (ShiftL IntType) [x, y] = assembleExprBinaryOp returnType IInt Ishl x y
    assembleExprOp returnType fc (ShiftR IntType) [x, y] = assembleExprBinaryOp returnType IInt Ishr x y
    assembleExprOp returnType fc (BAnd IntType) [x, y] = assembleExprBinaryOp returnType IInt Iand x y
    assembleExprOp returnType fc (BOr IntType) [x, y] = assembleExprBinaryOp returnType IInt Ior x y
    assembleExprOp returnType fc (BXOr IntType) [x, y] = assembleExprBinaryOp returnType IInt Ixor x y

    assembleExprOp returnType fc (Add IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "add"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp returnType inferredBigIntegerType op x y
    assembleExprOp returnType fc (Sub IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "subtract"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp returnType inferredBigIntegerType op x y
    assembleExprOp returnType fc (Mul IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "multiply"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp returnType inferredBigIntegerType op x y
    assembleExprOp returnType fc (Div IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "divide"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp returnType inferredBigIntegerType op x y
    assembleExprOp returnType fc (Mod IntegerType) [x, y] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "remainder"
                "(Ljava/math/BigInteger;)Ljava/math/BigInteger;" False
        in assembleExprBinaryOp returnType inferredBigIntegerType op x y
    assembleExprOp returnType fc (Neg IntegerType) [x] =
        let op = InvokeMethod InvokeVirtual "java/math/BigInteger" "negate"
                "()Ljava/math/BigInteger;" False
        in assembleExprUnaryOp returnType inferredBigIntegerType op x

    assembleExprOp returnType fc (Add DoubleType) [x, y] = assembleExprBinaryOp returnType IDouble Dadd x y
    assembleExprOp returnType fc (Sub DoubleType) [x, y] = assembleExprBinaryOp returnType IDouble Dsub x y
    assembleExprOp returnType fc (Mul DoubleType) [x, y] = assembleExprBinaryOp returnType IDouble Dmul x y
    assembleExprOp returnType fc (Div DoubleType) [x, y] = assembleExprBinaryOp returnType IDouble Ddiv x y
    assembleExprOp returnType fc (Neg DoubleType) [x] = assembleExprUnaryOp returnType IDouble Dneg x

    assembleExprOp returnType fc (LT CharType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmpge x y
    assembleExprOp returnType fc (LTE CharType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmpgt x y
    assembleExprOp returnType fc (EQ CharType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmpne x y
    assembleExprOp returnType fc (GTE CharType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmplt x y
    assembleExprOp returnType fc (GT CharType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmple x y

    assembleExprOp returnType fc (LT IntType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmpge x y
    assembleExprOp returnType fc (LTE IntType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmpgt x y
    assembleExprOp returnType fc (EQ IntType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmpne x y
    assembleExprOp returnType fc (GTE IntType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmplt x y
    assembleExprOp returnType fc (GT IntType) [x, y] = assembleExprBinaryBoolOp returnType IInt Ificmple x y

    assembleExprOp returnType fc (LT DoubleType) [x, y] =
        assembleExprBinaryBoolOp returnType IDouble (\label => do Dcmpg; Ifge label) x y
    assembleExprOp returnType fc (LTE DoubleType) [x, y] =
        assembleExprBinaryBoolOp returnType IDouble (\label => do Dcmpg; Ifgt label) x y
    assembleExprOp returnType fc (EQ DoubleType) [x, y] =
        assembleExprBinaryBoolOp returnType IDouble (\label => do Dcmpl; Ifne label) x y
    assembleExprOp returnType fc (GTE DoubleType) [x, y] =
        assembleExprBinaryBoolOp returnType IDouble (\label => do Dcmpl; Iflt label) x y
    assembleExprOp returnType fc (GT DoubleType) [x, y] =
        assembleExprBinaryBoolOp returnType IDouble (\label => do Dcmpl; Ifle label) x y

    assembleExprOp returnType fc (LT IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType bigIntegerClass Ifge x y
    assembleExprOp returnType fc (LTE IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType bigIntegerClass Ifgt x y
    assembleExprOp returnType fc (EQ IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType bigIntegerClass Ifne x y
    assembleExprOp returnType fc (GTE IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType bigIntegerClass Iflt x y
    assembleExprOp returnType fc (GT IntegerType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType bigIntegerClass Ifle x y

    assembleExprOp returnType fc (LT StringType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType stringClass Ifge x y
    assembleExprOp returnType fc (LTE StringType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType stringClass Ifgt x y
    assembleExprOp returnType fc (EQ StringType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType stringClass Ifne x y
    assembleExprOp returnType fc (GTE StringType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType stringClass Iflt x y
    assembleExprOp returnType fc (GT StringType) [x, y] =
        assembleExprComparableBinaryBoolOp returnType stringClass Ifle x y

    assembleExprOp returnType fc StrLength [x] = do
        assembleExpr False inferredStringType x
        InvokeMethod InvokeVirtual "java/lang/String" "length" "()I" False
        asmCast IInt returnType

    assembleExprOp returnType fc StrHead [x] = do
        assembleExpr False inferredStringType x
        Iconst 0
        InvokeMethod InvokeVirtual "java/lang/String" "charAt" "(I)C" False
        asmCast IChar returnType

    assembleExprOp returnType fc StrTail [x] = do
        assembleExpr False inferredStringType x
        Iconst 1
        InvokeMethod InvokeVirtual "java/lang/String" "substring" "(I)Ljava/lang/String;" False
        asmCast inferredStringType returnType

    assembleExprOp returnType fc StrIndex [x, i] = do
        assembleExpr False inferredStringType x
        assembleExpr False IInt i
        InvokeMethod InvokeVirtual "java/lang/String" "charAt" "(I)C" False
        asmCast IChar returnType

    assembleExprOp returnType fc StrCons [x, y] = assembleStrCons returnType x y

    assembleExprOp returnType fc StrAppend [x, y] =
        let op = InvokeMethod InvokeVirtual "java/lang/String" "concat" "(Ljava/lang/String;)Ljava/lang/String;" False
        in assembleExprBinaryOp returnType inferredStringType op x y

    assembleExprOp returnType fc StrReverse [x] = assembleStrReverse returnType x

    assembleExprOp returnType fc StrSubstr [offset, len, str] =do
        assembleExpr False IInt offset
        assembleExpr False IInt len
        assembleExpr False inferredStringType str
        InvokeMethod InvokeStatic (getRuntimeClass "Strings") "substring"
            "(IILjava/lang/String;)Ljava/lang/String;" False
        asmCast inferredStringType returnType

    {-assembleExprOp returnType fc  is Euler's number, which approximates to: 2.718281828459045
    assembleExprOp returnType fc DoubleExp [x] = op "exp" [x] -- Base is `e`. Same as: `pow(e, x)`
    assembleExprOp returnType fc DoubleLog [x] = op "log" [x] -- Base is `e`.
    assembleExprOp returnType fc DoubleSin [x] = op "sin" [x]
    assembleExprOp returnType fc DoubleCos [x] = op "cos" [x]
    assembleExprOp returnType fc DoubleTan [x] = op "tan" [x]
    assembleExprOp returnType fc DoubleASin [x] = op "asin" [x]
    assembleExprOp returnType fc DoubleACos [x] = op "acos" [x]
    assembleExprOp returnType fc DoubleATan [x] = op "atan" [x]
    assembleExprOp returnType fc DoubleSqrt [x] = op "sqrt" [x]
    assembleExprOp returnType fc DoubleFloor [x] = op "floor" [x]
    assembleExprOp returnType fc DoubleCeiling [x] = op "ceiling" [x]-}

    assembleExprOp returnType fc (Cast IntType StringType) [x] = do
        assembleExpr False IInt x
        InvokeMethod InvokeStatic "java/lang/Integer" "toString" "(I)Ljava/lang/String;" False
        asmCast inferredStringType returnType

    assembleExprOp returnType fc (Cast IntegerType StringType) [x] = do
        assembleExpr False inferredBigIntegerType x
        InvokeMethod InvokeVirtual "java/math/BigInteger" "toString" "()Ljava/lang/String;" False
        asmCast inferredBigIntegerType returnType

    assembleExprOp returnType fc (Cast DoubleType StringType) [x] = do
        assembleExpr False IDouble x
        InvokeMethod InvokeStatic "java/lang/Double" "toString" "(D)Ljava/lang/String;" False
        asmCast inferredStringType returnType

    assembleExprOp returnType fc (Cast CharType StringType) [x] = do
        assembleExpr False IChar x
        InvokeMethod InvokeStatic "java/lang/Character" "toString" "(I)Ljava/lang/String;" False
        asmCast inferredStringType returnType

    assembleExprOp returnType fc (Cast IntType IntegerType) [x] = do
        assembleExpr False IInt x
        I2l
        InvokeMethod InvokeStatic "java/math/BigInteger" "valueOf" "(J)Ljava/math/BigInteger;" False
        asmCast inferredBigIntegerType returnType

    assembleExprOp returnType fc (Cast DoubleType IntegerType) [x] = do
        assembleExpr False IDouble x
        D2i
        I2l
        InvokeMethod InvokeStatic "java/math/BigInteger" "valueOf" "(J)Ljava/math/BigInteger;" False
        asmCast inferredBigIntegerType returnType

    assembleExprOp returnType fc (Cast CharType IntegerType) [x] = do
        assembleExpr False IInt x
        I2l
        InvokeMethod InvokeStatic "java/math/BigInteger" "valueOf" "(J)Ljava/math/BigInteger;" False
        asmCast inferredBigIntegerType returnType

    assembleExprOp returnType fc (Cast StringType IntegerType) [x] = do
        New "java/math/BigInteger"
        Dup
        assembleExpr False inferredStringType x
        InvokeMethod InvokeSpecial "java/math/BigDecimal" "<init>" "(Ljava/lang/String;)V" False
        InvokeMethod InvokeVirtual "java/math/BigInteger" "toBigInteger" "()Ljava/math/BigInteger;" False
        asmCast inferredBigIntegerType returnType

    assembleExprOp returnType fc (Cast IntegerType IntType) [x] = do
        assembleExpr False inferredBigIntegerType x
        InvokeMethod InvokeVirtual "java/math/BigInteger" "intValue" "()I" False
        asmCast IInt returnType

    assembleExprOp returnType fc (Cast DoubleType IntType) [x] = do
        assembleExpr False IDouble x
        D2i
        asmCast IInt returnType

    assembleExprOp returnType fc (Cast StringType IntType) [x] = do
        assembleExpr False inferredStringType x
        InvokeMethod InvokeStatic "java/lang/Double" "parseDouble" "(Ljava/lang/String;)D" False
        D2i
        asmCast IInt returnType

    assembleExprOp returnType fc (Cast CharType IntType) [x] = do
        assembleExpr False IChar x
        asmCast IInt returnType

    assembleExprOp returnType fc (Cast IntegerType DoubleType) [x] = do
        assembleExpr False inferredBigIntegerType x
        InvokeMethod InvokeVirtual "java/math/BigInteger" "doubleValue" "()D" False
        asmCast IDouble returnType

    assembleExprOp returnType fc (Cast IntType DoubleType) [x] = do
        assembleExpr False IInt x
        I2d
        asmCast IDouble returnType

    assembleExprOp returnType fc (Cast StringType DoubleType) [x] = do
        assembleExpr False inferredStringType x
        InvokeMethod InvokeStatic "java/lang/Double" "parseDouble" "(Ljava/lang/String;)D" False
        asmCast IDouble returnType

    assembleExprOp returnType fc (Cast IntType CharType) [x] = do
        assembleExpr False IInt x
        I2c
        asmCast IChar returnType

    assembleExprOp returnType fc BelieveMe [_,_,x] = do
        assembleExpr False IUnknown x
        asmCast IUnknown returnType

    assembleExprOp returnType fc Crash [_, msg] = do
        assembleExpr False inferredStringType msg
        InvokeMethod InvokeStatic runtimeClass "crash" "(Ljava/lang/String;)Ljava/lang/Object;" False
        asmCast inferredObjectType returnType

    assembleExprOp returnType fc op _ = Throw fc ("Unsupported operator " ++ show op)

    assembleParameter : (NamedCExp, InferredType) -> Asm ()
    assembleParameter (param, ty) = assembleExpr False ty param

    storeParameter : (Nat, NamedCExp, InferredType) -> Asm ()
    storeParameter (var, (NmLocal _ loc), ty) = do
        let valueVariableName = jvmSimpleName loc
        valueVariableIndex <- getVariableIndex valueVariableName
        if var == valueVariableIndex then Pure ()
        else do
            valueVariableType <- getVariableType valueVariableName
            loadVar !getVariableTypes valueVariableType ty valueVariableIndex
            storeVar ty ty var
    storeParameter (var, param, ty) = do
        assembleExpr False ty param
        storeVar ty ty var

    assembleSubMethodWithScope : (isTailCall: Bool) -> InferredType -> (parameterValue: Maybe NamedCExp) ->
        (parameterName : Maybe Name) -> NamedCExp -> Asm ()
    assembleSubMethodWithScope isTailCall returnType (Just value) (Just name) body = do
        parentScope <- getScope !getCurrentScopeIndex
        parameterValueVariableIndex <- newDynamicVariableIndex
        let parameterValueVariable = jvmSimpleName name ++ show parameterValueVariableIndex
        withScope $ assembleSubMethod isTailCall returnType (Just (assembleValue parentScope parameterValueVariable))
            (Just $ UN parameterValueVariable) parentScope
            (substituteVariableSubMethodBody (NmLocal (getFC body) $ UN parameterValueVariable) body)
      where
          assembleValue : Scope -> String -> Asm ()
          assembleValue enclosingScope variableName = do
            lambdaScopeIndex <- getCurrentScopeIndex
            updateCurrentScopeIndex (index enclosingScope)
            assembleExpr False !(getVariableType variableName) value
            updateCurrentScopeIndex lambdaScopeIndex

    assembleSubMethodWithScope isTailCall returnType _ parameterName body = do
        parentScope <- getScope !getCurrentScopeIndex
        withScope $ assembleSubMethod isTailCall returnType Nothing parameterName parentScope body

    assembleSubMethod : (isTailCall: Bool) -> InferredType -> (parameterValueExpr: (Maybe (Asm ()))) ->
        (parameterName: Maybe Name) -> Scope -> NamedCExp -> Asm ()
    assembleSubMethod isTailCall lambdaReturnType parameterValueExpr parameterName declaringScope expr = do
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
            when isTailCall $
                if isExtracted then asmReturn implementationMethodReturnType
                else asmReturn lambdaInterfaceType
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
            let lambdaReturnType = if lambdaType == ThunkLambda then thunkType else inferredObjectType
            assembleExpr True lambdaReturnType expr
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

    assembleMissingDefault :InferredType -> FC -> String -> Asm ()
    assembleMissingDefault returnType fc defaultLabel = do
        LabelStart defaultLabel
        assembleExpr True returnType (NmCrash fc "Unreachable code")

    assembleConstantSwitch : (returnType: InferredType) -> (switchExprType: InferredType) -> FC ->
        NamedCExp -> List NamedConstAlt -> Maybe NamedCExp -> Asm ()
    assembleConstantSwitch _ _ fc _ [] _ = Throw fc "Empty cases"

    assembleConstantSwitch returnType IInt fc sc alts def = do
        assembleExpr False IInt sc
        switchCases <- getCasesWithLabels alts
        let labels = fst <$> switchCases
        let exprs = second <$> switchCases
        traverse_ CreateLabel labels
        defaultLabel <- createDefaultLabel
        LookupSwitch defaultLabel labels exprs
        let switchCasesWithEndLabel = getSwitchCasesWithEndLabel switchCases labels
        traverse_ assembleExprConstAlt switchCasesWithEndLabel
        maybe (assembleMissingDefault returnType fc defaultLabel) (assembleDefault defaultLabel) def
      where
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
            assembleExpr True returnType expr

        assembleDefault : String -> NamedCExp -> Asm ()
        assembleDefault defaultLabel expr =  assembleCaseWithScope defaultLabel methodEndLabel expr

        assembleExprConstAlt : (String, Int, NamedConstAlt, String) -> Asm ()
        assembleExprConstAlt (labelStart, _, (MkNConstAlt _ expr), labelEnd) =
            assembleCaseWithScope labelStart labelEnd expr

    assembleConstantSwitch returnType constantType fc sc alts def = do
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
            assembleExpr False constantType sc
            storeVar constantType constantType constantExprVariableIndex
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
            assembleConstantSwitch returnType IInt fc (NmLocal fc $ UN hashCodePositionVariableName)
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

    assembleConCaseExpr : InferredType -> Nat -> Name -> List Name -> NamedCExp -> Asm ()
    assembleConCaseExpr returnType idrisObjectVariableIndex name args expr = do
            bindArg 0 args
            assembleExpr True returnType expr
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

    assembleConstructorSwitch : InferredType -> FC -> Nat -> List NamedConAlt -> Maybe NamedCExp -> Asm ()
    assembleConstructorSwitch returnType fc idrisObjectVariableIndex alts def = do
            switchCases <- getCasesWithLabels alts
            let labels = fst <$> switchCases
            let switchCasesWithEndLabel = getSwitchCasesWithEndLabel switchCases labels
            let exprs = caseExpression <$> switchCases
            traverse_ CreateLabel labels
            defaultLabel <- createDefaultLabel
            LookupSwitch defaultLabel labels exprs
            traverse_ assembleExprConAlt switchCasesWithEndLabel
            maybe (assembleMissingDefault returnType fc defaultLabel) (assembleDefault defaultLabel) def
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
                assembleExpr True returnType expr

            assembleCaseWithScope : String -> String -> Name -> List Name -> NamedCExp -> Asm ()
            assembleCaseWithScope labelStart labelEnd name args expr = withScope $ do
                scopeIndex <- getCurrentScopeIndex
                scope <- getScope scopeIndex
                let (lineNumberStart, lineNumberEnd) = lineNumbers scope
                LabelStart labelStart
                addLineNumber lineNumberStart labelStart
                updateScopeStartLabel scopeIndex labelStart
                updateScopeEndLabel scopeIndex labelEnd
                assembleConCaseExpr returnType idrisObjectVariableIndex name args expr

            assembleExprConAlt : (String, Int, NamedConAlt, String) -> Asm ()
            assembleExprConAlt (labelStart, _, (MkNConAlt name tag args expr), labelEnd) =
                assembleCaseWithScope labelStart labelEnd name args expr

        assembleStringConstructorSwitch : InferredType -> FC -> Nat -> List NamedConAlt ->
            Maybe NamedCExp -> Asm ()
        assembleStringConstructorSwitch returnType fc idrisObjectVariableIndex alts def = do
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
            assembleExpr False IInt (NmLocal fc $ UN hashCodePositionVariableName)
            assembleConstructorSwitch returnType fc idrisObjectVariableIndex
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

    jvmExtPrim : InferredType -> ExtPrim -> List NamedCExp -> Asm ()
    jvmExtPrim returnType JvmInstanceMethodCall [ret, NmPrimVal fc (Str fn), fargs, world] = do
        (obj :: instanceMethodArgs) <- getFArgs fargs
            | [] => Throw fc ("JVM instance method must have at least one argument " ++ fn)
        let args = obj :: instanceMethodArgs
        argTypes <- traverse tySpec (map fst args)
        methodReturnType <- tySpec ret
        traverse assembleParameter $ List.zip (map snd args) argTypes
        let methodDescriptor = getMethodDescriptor $ MkInferredFunctionType methodReturnType $ drop 1 argTypes
        let (cname, mnameWithDot) = break (== '.') fn
        let (_, mname) = break (/= '.') mnameWithDot
        InvokeMethod InvokeVirtual cname mname methodDescriptor False
        asmCast methodReturnType returnType
    jvmExtPrim returnType JvmStaticMethodCall [ret, NmPrimVal fc (Str fn), fargs, world] = do
        args <- getFArgs fargs
        argTypes <- traverse tySpec (map fst args)
        methodReturnType <- tySpec ret
        traverse assembleParameter $ List.zip (map snd args) argTypes
        let methodDescriptor = getMethodDescriptor $ MkInferredFunctionType methodReturnType argTypes
        let (cname, mnameWithDot) = break (== '.') fn
        let (_, mname) = break (/= '.') mnameWithDot
        InvokeMethod InvokeStatic cname mname methodDescriptor False
        asmCast methodReturnType returnType
    jvmExtPrim returnType NewArray [_, size, val, world] = do
        assembleExpr False IInt size
        assembleExpr False IUnknown val
        InvokeMethod InvokeStatic arraysClass "create" "(ILjava/lang/Object;)Ljava/util/ArrayList;" False
        asmCast arrayListType returnType
    jvmExtPrim returnType ArrayGet [_, arr, pos, world] = do
        assembleExpr False arrayListType arr
        assembleExpr False IInt pos
        InvokeMethod InvokeVirtual arrayListClass "get" "(I)Ljava/lang/Object;" False
        asmCast inferredObjectType returnType
    jvmExtPrim returnType ArraySet [_, arr, pos, val, world] = do
        assembleExpr False arrayListType arr
        assembleExpr False IInt pos
        assembleExpr False IUnknown val
        InvokeMethod InvokeVirtual arrayListClass "set" "(ILjava/lang/Object;)Ljava/lang/Object;" False
        asmCast inferredObjectType returnType
    jvmExtPrim returnType NewIORef [_, val, world] = do
        New refClass
        Dup
        assembleExpr False IUnknown val
        InvokeMethod InvokeSpecial refClass "<init>" "(Ljava/lang/Object;)V" False
        asmCast refType returnType
    jvmExtPrim returnType ReadIORef [_, ref, world] = do
        assembleExpr False refType ref
        InvokeMethod InvokeVirtual refClass "getValue" "()Ljava/lang/Object;" False
        asmCast inferredObjectType returnType
    jvmExtPrim returnType WriteIORef [_, ref, val, world] = do
        assembleExpr False refType ref
        assembleExpr False IUnknown val
        InvokeMethod InvokeVirtual refClass "setValue" "(Ljava/lang/Object;)V" False
        Aconstnull
        asmCast inferredObjectType returnType
    jvmExtPrim _ prim args = Throw emptyFC ("Unsupported external function " ++ show prim)

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
        assembleExpr True methodReturnType optimizedExpr
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
