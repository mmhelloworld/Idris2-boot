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

enterScope : (shouldAddLineNumber: Bool) -> Asm ()
enterScope shouldAddLineNumber = do
    scopeIndex <- freshScopeIndex
    updateCurrentScopeIndex scopeIndex
    when shouldAddLineNumber $ do
        scope <- getScope scopeIndex
        let lineNumberStart = fst $ lineNumbers scope
        label <- freshLabel
        CreateLabel label
        LabelStart label
        addLineNumber lineNumberStart label
        updateScopeStartLabel scopeIndex label

exitScope : (shouldAddLineNumber: Bool) -> Scope -> Asm ()
exitScope shouldAddLineNumber targetScope = do
    scopeIndex <- getCurrentScopeIndex
    when shouldAddLineNumber $ do
        scope <- getScope scopeIndex
        let lineNumberEnd = snd $ lineNumbers scope
        label <- freshLabel
        CreateLabel label
        LabelStart label
        addLineNumber lineNumberEnd label
        updateScopeEndLabel scopeIndex label
    updateCurrentScopeIndex $ index targetScope

withScope : (shouldAddLineNumber: Bool) -> Lazy (Asm ()) -> Asm ()
withScope shouldAddLineNumber op = do
    scope <- getScope !getCurrentScopeIndex
    enterScope shouldAddLineNumber
    op
    exitScope shouldAddLineNumber scope

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
        label <- freshLabel
        Pure (label, constExpr, alt)

constantAltHashCodeExpr : FC -> (Nat, NamedConstAlt) -> Asm (Int, Nat, NamedConstAlt)
constantAltHashCodeExpr fc positionAndAlt@(position, MkNConstAlt constant _) = do
        constExpr <- hashCode constant
        Pure (constExpr, position, snd positionAndAlt)
    where
        hashCode : TT.Constant -> Asm Int
        hashCode (BI value) = LiftIo $ invokeInstance "hashCode" (Integer -> JVM_IO Int) value
        hashCode (Str value) = LiftIo $ invokeInstance "hashCode" (String -> JVM_IO Int) value
        hashCode x = Throw fc ("Constant " ++ show x ++ " cannot be compiled to 'Switch'.")

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
conAltIntExpr alt@(MkNConAlt _ tag _ expr) = do
    label <- freshLabel
    Pure (label, fromMaybe 0 tag, alt)

createDefaultLabel : String -> Maybe NamedCExp -> Asm String
createDefaultLabel switchEndLabel Nothing = Pure switchEndLabel
createDefaultLabel _ _ = do
    label <- freshLabel
    CreateLabel label
    Pure label

getSwitchCasesWithEndLabel : List (String, Int, a) -> List String ->  String ->
    List (String, Int, a, String)
getSwitchCasesWithEndLabel switchCases labelStarts switchEndLabel =
        go $ List.zip switchCases (drop 1 labelStarts ++ [switchEndLabel])
    where
        go : List ((String, Int, a), String) -> List (String, Int, a, String)
        go (((labelStart, constExpr, body), labelEnd) :: xs) = (labelStart, constExpr, body, labelEnd) :: go xs
        go [] = []

mutual
    assembleExpr : (ret : Asm ()) -> InferredType -> NamedCExp -> Asm ()

    assembleExpr ret returnType (NmDelay _ expr) = assembleLambda ret returnType Nothing expr

    assembleExpr ret returnType (NmLocal _ loc) = do
        let variableName = jvmSimpleName loc
        variableType <- getVariableType variableName
        index <- getVariableIndex variableName
        variableTypes <- getVariableTypes
        loadVar variableTypes variableType returnType index
        ret

    assembleExpr ret returnType (NmLam _ parameter body) = assembleLambda ret returnType (Just parameter) body

    assembleExpr ret returnType (NmLet _ var value expr) = do
        withScope True $ do
            let variableName = jvmSimpleName var
            variableType <- getVariableType variableName
            variableIndex <- getVariableIndex variableName

            withScope True $ assembleExpr (storeVar variableType variableType variableIndex)
                variableType value

            withScope True $ assembleExpr ret returnType expr

    assembleExpr _ returnType app@(NmApp fc (NmRef nameFc (UN ":__jvmTailRec__:")) args) = -- Tail recursion
        case length args of
            Z => Pure () -- No arguments to store
            (S lastArgIndex) => do
                jname <- idrisName <$> getCurrentFunction
                parameterTypes <- getFunctionParameterTypes jname
                let argsWithTypes = List.zip args parameterTypes
                traverse_ storeParameter $ List.zip [0 .. lastArgIndex] argsWithTypes

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
        New constructorClassName
        Dup
        Iconst $ fromMaybe 0 tag
        let constructorParameterCount = length args
        let constructorTypes = IInt :: replicate constructorParameterCount inferredObjectType
        let argsWithTypes = List.zip args $ drop 1 constructorTypes
        traverse assembleParameter argsWithTypes
        let descriptor = getMethodDescriptor $ MkInferredFunctionType IVoid constructorTypes
        CreateIdrisConstructorClass constructorClassName constructorParameterCount
        InvokeMethod InvokeSpecial constructorClassName "<init>" descriptor False
        asmCast (IRef constructorClassName) returnType
        ret

    assembleExpr ret returnType (NmOp fc fn args) = assembleExprOp ret returnType fc fn args
    assembleExpr ret returnType (NmExtPrim fc p args) = jvmExtPrim ret returnType (toPrim p) args
    assembleExpr ret returnType (NmForce _ expr) = assembleExpr ret1 thunkType expr where
        ret1 : Asm ()
        ret1 = do
            InvokeMethod InvokeStatic runtimeClass "unwrap" "(Ljava/lang/Object;)Ljava/lang/Object;" False
            asmCast inferredObjectType returnType
            ret

    assembleExpr ret returnType (NmConCase fc sc [] Nothing) = do defaultValue returnType; ret
    assembleExpr ret returnType (NmConCase fc sc [] (Just expr)) = do
        dynamicVariableIndex <- freshDynamicVariableIndex
        let idrisObjectVariableName = "constructorSwitchValue" ++ show dynamicVariableIndex
        idrisObjectVariableIndex <- getVariableIndex idrisObjectVariableName
        assembleExpr (storeVar idrisObjectType idrisObjectType idrisObjectVariableIndex) idrisObjectType sc
        assembleExpr ret returnType expr
    assembleExpr ret returnType (NmConCase fc sc [MkNConAlt name _ args expr] Nothing) = do
        dynamicVariableIndex <- freshDynamicVariableIndex
        let idrisObjectVariableName = "constructorSwitchValue" ++ show dynamicVariableIndex
        idrisObjectVariableIndex <- getVariableIndex idrisObjectVariableName
        assembleExpr (storeVar idrisObjectType idrisObjectType idrisObjectVariableIndex) idrisObjectType sc
        assembleConCaseExpr ret returnType idrisObjectVariableIndex name args expr
    assembleExpr ret returnType (NmConCase fc sc alts def) = do
        let idrisObjectVariableName = "constructorSwitchValue" ++ show !freshDynamicVariableIndex
        idrisObjectVariableIndex <- getVariableIndex idrisObjectVariableName
        assembleExpr (storeVar idrisObjectType idrisObjectType idrisObjectVariableIndex) idrisObjectType sc
        loadVar !getVariableTypes idrisObjectType idrisObjectType idrisObjectVariableIndex
        InvokeMethod InvokeInterface idrisObjectClass "getConstructorId" "()I" True
        assembleConstructorSwitch ret returnType fc idrisObjectVariableIndex alts def
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
    assembleExprBinaryBoolOp ret returnType exprType operator expr1 expr2 =  do
        dynamicVariableIndex <- freshDynamicVariableIndex
        let boolOpResultVariable = "jvm$boolOpResult" ++ show dynamicVariableIndex
        boolOpResultVariableIndex <- getVariableIndex boolOpResultVariable
        Iconst (-1)
        storeVar IBool IBool boolOpResultVariableIndex
        assembleExpr (assembleExpr (ret1 boolOpResultVariableIndex) exprType expr2) exprType expr1
      where
        ret1 : Nat -> Asm ()
        ret1 resultVariableIndex = do
            ifLabel <- freshLabel
            CreateLabel ifLabel
            elseLabel <- freshLabel
            CreateLabel elseLabel
            endLabel <- freshLabel
            CreateLabel endLabel
            operator elseLabel
            LabelStart ifLabel
            scope <- getScope !getCurrentScopeIndex
            Iconst 1
            storeVar IBool IBool resultVariableIndex
            Goto endLabel
            LabelStart elseLabel
            Iconst 0
            storeVar IBool IBool resultVariableIndex
            LabelStart endLabel
            loadVar !getVariableTypes IBool IBool resultVariableIndex
            ret

    assembleExprComparableBinaryBoolOp : Asm () -> InferredType -> String -> (String -> Asm ()) ->
        NamedCExp -> NamedCExp -> Asm ()
    assembleExprComparableBinaryBoolOp ret returnType className operator expr1 expr2 =  do
        dynamicVariableIndex <- freshDynamicVariableIndex
        let boolOpResultVariable = "jvm$boolOpResult" ++ show dynamicVariableIndex
        boolOpResultVariableIndex <- getVariableIndex boolOpResultVariable
        Iconst (-1)
        storeVar IBool IBool boolOpResultVariableIndex
        let exprType = IRef className
        assembleExpr (assembleExpr (ret1 boolOpResultVariableIndex) exprType expr2) exprType expr1
      where
        ret1 : Nat -> Asm ()
        ret1 resultVariableIndex = do
            ifLabel <- freshLabel
            CreateLabel ifLabel
            elseLabel <- freshLabel
            CreateLabel elseLabel
            endLabel <- freshLabel
            CreateLabel endLabel
            InvokeMethod InvokeVirtual className "compareTo" ("(L" ++ className ++ ";)I") False
            operator elseLabel
            LabelStart ifLabel
            scope <- getScope !getCurrentScopeIndex
            Iconst 1
            storeVar IBool IBool resultVariableIndex
            Goto endLabel
            LabelStart elseLabel
            Iconst 0
            storeVar IBool IBool resultVariableIndex
            LabelStart endLabel
            loadVar !getVariableTypes IBool IBool resultVariableIndex
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
            InvokeMethod InvokeSpecial "java/math/BigInteger" "<init>" "(Ljava/lang/String;)V" False
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
            InvokeMethod InvokeStatic "java/lang/Integer" "parseInt" "(Ljava/lang/String;)I" False
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
    storeParameter (var, param, ty) = assembleExpr (storeVar ty ty var) ty param

    assembleLambda : Asm () -> InferredType -> (param : Maybe Name) -> NamedCExp -> Asm ()
    assembleLambda ret returnType param body = do
         parentScope <- getScope !getCurrentScopeIndex
         withScope False $ assembleInvokeDynamic returnType param parentScope body
         ret

    assembleInvokeDynamic : InferredType -> (parameterName: Maybe Name) -> Scope -> NamedCExp -> Asm ()
    assembleInvokeDynamic lambdaReturnType parameterName declaringScope expr = do
            scope <- getScope !getCurrentScopeIndex
            maybe (Pure ()) (\value => setScopeCounter (value + 1)) (parentIndex scope)
            let lambdaBodyReturnType = returnType scope
            let lambdaInterfaceType = getLambdaInterfaceType parameterName lambdaBodyReturnType
            className <- getClassName
            parameterTypes <- traverse getVariableType (jvmSimpleName <$> parameterName)
            let variableTypes = SortedMap.values !(loadClosures declaringScope scope)
            let invokeDynamicDescriptor = getMethodDescriptor $ MkInferredFunctionType lambdaInterfaceType variableTypes
            let implementationMethodReturnType =
                if lambdaInterfaceType == inferredLambdaType then inferredObjectType
                else thunkType
            let implementationMethodDescriptor = getMethodDescriptor $
                MkInferredFunctionType implementationMethodReturnType (variableTypes ++ toList parameterTypes)
            let instantiatedMethodDescriptor = getMethodDescriptor $
                MkInferredFunctionType implementationMethodReturnType $ toList parameterTypes
            lambdaMethodName <- getLambdaImplementationMethodName
            let interfaceMethodName = if lambdaInterfaceType == inferredLambdaType then "apply" else "evaluate"
            let samDesc = if lambdaInterfaceType == inferredLambdaType then "(Ljava/lang/Object;)Ljava/lang/Object;"
                else "()Lio/github/mmhelloworld/idris2boot/runtime/Thunk;"
            invokeDynamic className lambdaMethodName interfaceMethodName invokeDynamicDescriptor
                samDesc implementationMethodDescriptor instantiatedMethodDescriptor
            when (lambdaReturnType /= inferredObjectType) $ asmCast lambdaInterfaceType lambdaReturnType
            state <- GetState
            let oldLineNumberLabels = lineNumberLabels state
            updateState $ record { lineNumberLabels = SortedMap.empty }
            CreateMethod [Private, Static, Synthetic] "" className lambdaMethodName implementationMethodDescriptor
                Nothing Nothing [] []
            MethodCodeStart
            labelStart <- freshLabel
            labelEnd <- freshLabel
            addLambdaStartLabel scope labelStart
            maybe (Pure ()) (\parentScopeIndex => updateScopeStartLabel parentScopeIndex labelStart) (parentIndex scope)
            assembleExpr (castReturn lambdaInterfaceType lambdaBodyReturnType) lambdaBodyReturnType expr
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

            castReturn : InferredType -> InferredType -> Asm ()
            castReturn lambdaInterfaceType returnType =
                if lambdaInterfaceType == inferredLambdaType then do
                    asmCast returnType inferredObjectType
                    asmReturn inferredObjectType
                else if returnType == IVoid then do Aconstnull; asmReturn thunkType
                else if isThunkType returnType then asmReturn returnType
                else do asmCast returnType thunkType; asmReturn thunkType

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

    assembleConstantSwitch : Asm () -> (returnType: InferredType) -> (switchExprType: InferredType) -> FC ->
        NamedCExp -> List NamedConstAlt -> Maybe NamedCExp -> Asm ()
    assembleConstantSwitch _ _ _ fc _ [] _ = Throw fc "Empty cases"

    assembleConstantSwitch ret returnType IInt fc sc alts def = assembleExpr ret1 IInt sc where

        getCasesWithLabels : List NamedConstAlt -> Asm (List (String, Int, NamedConstAlt))
        getCasesWithLabels alts = do
            caseExpressionsWithLabels <- traverse (constantAltIntExpr fc) alts
            Pure $ sortBy (comparing second) caseExpressionsWithLabels

        assembleCaseWithScope : String -> String -> NamedCExp -> Asm ()
        assembleCaseWithScope labelStart labelEnd expr = withScope False $ do
                scopeIndex <- getCurrentScopeIndex
                scope <- getScope scopeIndex
                let (lineNumberStart, lineNumberEnd) = lineNumbers scope
                LabelStart labelStart
                updateScopeStartLabel scopeIndex labelStart
                addLineNumber lineNumberStart labelStart
                assembleExpr ret returnType expr
                updateScopeEndLabel scopeIndex labelEnd

        assembleExprConstAlt : String -> (String, Int, NamedConstAlt, String) -> Asm ()
        assembleExprConstAlt switchEndLabel (labelStart, _, (MkNConstAlt _ expr), labelEnd) = do
            assembleCaseWithScope labelStart labelEnd expr
            Goto switchEndLabel

        ret1 : Asm ()
        ret1 = do
            switchCases <- getCasesWithLabels alts
            let labels = fst <$> switchCases
            let exprs = second <$> switchCases
            switchEndLabel <- freshLabel
            CreateLabel switchEndLabel
            traverse_ CreateLabel labels
            defaultLabel <- createDefaultLabel switchEndLabel def
            LookupSwitch defaultLabel labels exprs
            let switchCasesWithEndLabel = getSwitchCasesWithEndLabel switchCases labels switchEndLabel
            traverse_ (assembleExprConstAlt switchEndLabel) switchCasesWithEndLabel
            maybe (Pure ()) (assembleCaseWithScope defaultLabel switchEndLabel) def
            LabelStart switchEndLabel

    assembleConstantSwitch ret returnType constantType fc sc alts def = do
            constantExprVariableSuffixIndex <- freshDynamicVariableIndex
            let constantExprVariableName = "constantCaseExpr" ++ show constantExprVariableSuffixIndex
            constantExprVariableIndex <- getVariableIndex constantExprVariableName
            hashCodePositionVariableSuffixIndex <- freshDynamicVariableIndex
            let hashCodePositionVariableName = "hashCodePosition" ++ show hashCodePositionVariableSuffixIndex
            hashCodePositionVariableIndex <- getVariableIndex hashCodePositionVariableName
            hashPositionAndAlts <- traverse (constantAltHashCodeExpr fc) $ List.zip [0 .. length $ drop 1 alts] alts
            let positionAndAltsByHash = multiValueMap fst snd hashPositionAndAlts
            hashCodeSwitchCases <- getHashCodeCasesWithLabels positionAndAltsByHash
            let labels = fst <$> hashCodeSwitchCases
            let exprs = second <$> hashCodeSwitchCases
            switchEndLabel <- freshLabel
            CreateLabel switchEndLabel
            traverse_ CreateLabel labels
            assembleExpr (storeVar constantType constantType !(getVariableIndex constantExprVariableName))
                constantType sc
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
            labelHashCodeAlt : (Int, a) -> Asm (String, Int, a)
            labelHashCodeAlt (hash, expressions) = Pure (!freshLabel, hash, expressions)

            hashPositionSwitchAlts : List (Int, Nat, NamedConstAlt) -> List NamedConstAlt
            hashPositionSwitchAlts exprPositionAlts = reverse $ go [] exprPositionAlts where
                go : List NamedConstAlt -> List (Int, Nat, NamedConstAlt) -> List NamedConstAlt
                go acc [] = acc
                go acc ((_, position, (MkNConstAlt _ expr)) :: alts) =
                    go (MkNConstAlt (I $ cast position) expr :: acc) alts

            getHashCodeCasesWithLabels : SortedMap Int (List (Nat, NamedConstAlt)) ->
                Asm (List (String, Int, List (Nat, NamedConstAlt)))
            getHashCodeCasesWithLabels positionAndAltsByHash =
                traverse labelHashCodeAlt $ SortedMap.toList positionAndAltsByHash

            assembleHashCodeSwitchCases : FC -> String -> Nat -> Nat -> String ->
                (String, Int, List (Nat, NamedConstAlt)) -> Asm ()
            assembleHashCodeSwitchCases fc _ _ _ _ (_, _, []) = Throw fc "Empty cases"
            assembleHashCodeSwitchCases fc constantClass constantExprVariableIndex hashCodePositionVariableIndex
                switchEndLabel (label, _, positionAndAlts) =
                    go label positionAndAlts where
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
                            nextLabel <- freshLabel
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

    assembleConstructorSwitch : Asm () -> InferredType -> FC -> Nat -> List NamedConAlt -> Maybe NamedCExp -> Asm ()
    assembleConstructorSwitch ret returnType fc idrisObjectVariableIndex alts def = do
            switchCases <- getCasesWithLabels alts
            let labels = fst <$> switchCases
            switchEndLabel <- freshLabel
            let switchCasesWithEndLabel = getSwitchCasesWithEndLabel switchCases labels switchEndLabel
            let exprs = caseExpression <$> switchCases
            CreateLabel switchEndLabel
            traverse_ CreateLabel labels
            defaultLabel <- createDefaultLabel switchEndLabel def
            LookupSwitch defaultLabel labels exprs
            traverse_ (assembleExprConAlt switchEndLabel) switchCasesWithEndLabel
            maybe (Pure ()) (assembleDef defaultLabel switchEndLabel) def
            scope <- getScope !getCurrentScopeIndex
            let lineNumberStart = fst $ lineNumbers scope
            LabelStart switchEndLabel
            addLineNumber lineNumberStart switchEndLabel
        where
            caseExpression : (String, Int, NamedConAlt) -> Int
            caseExpression (_, expr, _) = expr

            getCasesWithLabels : List NamedConAlt -> Asm (List (String, Int, NamedConAlt))
            getCasesWithLabels alts = do
                caseExpressionsWithLabels <- traverse conAltIntExpr alts
                Pure $ sortBy (comparing caseExpression) caseExpressionsWithLabels

            assembleDef : String -> String -> NamedCExp -> Asm ()
            assembleDef labelStart labelEnd expr = withScope False $ do
                scopeIndex <- getCurrentScopeIndex
                scope <- getScope scopeIndex
                let lineNumberStart = fst $ lineNumbers scope
                LabelStart labelStart
                addLineNumber lineNumberStart labelStart
                updateScopeStartLabel scopeIndex labelStart
                assembleExpr ret returnType expr
                updateScopeEndLabel scopeIndex labelEnd

            assembleCaseWithScope : String -> String -> Name -> List Name -> NamedCExp -> Asm ()
            assembleCaseWithScope labelStart labelEnd name args expr = withScope False $ do
                scopeIndex <- getCurrentScopeIndex
                scope <- getScope scopeIndex
                let lineNumberStart = fst $ lineNumbers scope
                LabelStart labelStart
                addLineNumber lineNumberStart labelStart
                updateScopeStartLabel scopeIndex labelStart
                assembleConCaseExpr ret returnType idrisObjectVariableIndex name args expr
                updateScopeEndLabel scopeIndex labelEnd

            assembleExprConAlt : String -> (String, Int, NamedConAlt, String) -> Asm ()
            assembleExprConAlt switchEndLabel (labelStart, _, (MkNConAlt name tag args expr), labelEnd) = do
                assembleCaseWithScope labelStart labelEnd name args expr
                Goto switchEndLabel

    jvmExtPrim : Asm () -> InferredType -> ExtPrim -> List NamedCExp -> Asm ()
    jvmExtPrim returns returnType JvmStaticMethodCall [ret, NmPrimVal fc (Str fn), fargs, world]
      = do args <- getFArgs fargs
           argTypes <- traverse tySpec (map fst args)
           methodReturnType <- tySpec ret
           traverse assembleParameter $ List.zip (map snd args) argTypes
           let methodDescriptor = getMethodDescriptor $ MkInferredFunctionType methodReturnType argTypes
           let (cname, mnameWithDot) = break (== '.') fn
           let (_, mname) = break (/= '.') mnameWithDot
           InvokeMethod InvokeStatic cname mname methodDescriptor False
           asmCast methodReturnType returnType
           returns
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
        labelCounter = 0,
        lineNumberLabels = SortedMap.empty }
    updateCurrentFunction $ record { dynamicVariableCounter = 0 }
    let optimizedExpr = optimizedBody function
    CreateMethod [Public, Static] fileName declaringClassName methodName descriptor Nothing Nothing [] []
    MethodCodeStart
    methodStartLabel <- freshLabel
    CreateLabel methodStartLabel
    methodEndLabel <- freshLabel
    CreateLabel methodEndLabel
    LabelStart methodStartLabel
    let hasResultVariable = needResultVariable function
    withScope False $ do
        scopeIndex <- getCurrentScopeIndex
        scope <- getScope scopeIndex
        let (lineNumberStart, lineNumberEnd) = lineNumbers scope
        addLineNumber lineNumberStart methodStartLabel
        updateScopeStartLabel scopeIndex methodStartLabel
        resultVariableIndex <-
            if hasResultVariable then do
                resultVariable <- getVariableIndex $ "jvm$fn$res" ++ show !freshDynamicVariableIndex
                Pure $ Just resultVariable
            else Pure Nothing
        maybe (Pure ())
            (\resultVariable => do
                defaultValue methodReturnType
                storeVar methodReturnType methodReturnType resultVariable)
            resultVariableIndex
        if hasSelfTailCall $ tailCallCategory function then do
            tailRecursionLoopVariableIndex <- getVariableIndex $ "jvm$rec$loop" ++ show !freshDynamicVariableIndex
            Iconst 1
            storeVar IInt IInt tailRecursionLoopVariableIndex
            tailRecStartLabelName <- freshLabel
            tailRecEndLabelName <- freshLabel
            CreateLabel tailRecStartLabelName
            LabelStart tailRecStartLabelName
            loadVar !getVariableTypes IInt IInt tailRecursionLoopVariableIndex
            CreateLabel tailRecEndLabelName
            Ifeq tailRecEndLabelName
            assembleExpr (endTailRecursion tailRecursionLoopVariableIndex resultVariableIndex methodReturnType)
                methodReturnType optimizedExpr
            Goto tailRecStartLabelName
            LabelStart tailRecEndLabelName
            loadResultAndReturn methodReturnType scopeIndex methodEndLabel resultVariableIndex
        else do
            assembleExpr (storeResult methodReturnType resultVariableIndex) methodReturnType optimizedExpr
            loadResultAndReturn methodReturnType scopeIndex methodEndLabel resultVariableIndex
    addLocalVariables 0
    MaxStackAndLocal (-1) (-1)
    MethodCodeEnd
  where
    storeResult : InferredType -> Maybe Nat -> Asm ()
    storeResult _ Nothing = Pure ()
    storeResult methodReturnType (Just resultVariableIndex) = when (methodReturnType /= IVoid) $
        storeVar methodReturnType methodReturnType resultVariableIndex

    endTailRecursion : Nat -> Maybe Nat -> InferredType -> Asm ()
    endTailRecursion tailRecursionLoopVariableIndex resultVariableIndex methodReturnType = do
        storeResult methodReturnType resultVariableIndex
        Iconst 0
        storeVar IInt IInt tailRecursionLoopVariableIndex

    loadResultAndReturn : InferredType -> Nat -> String -> Maybe Nat -> Asm ()
    loadResultAndReturn methodReturnType scopeIndex methodEndLabel Nothing = do
        asmReturn methodReturnType
        LabelStart methodEndLabel
        updateScopeEndLabel scopeIndex methodEndLabel
    loadResultAndReturn methodReturnType scopeIndex methodEndLabel (Just resultVariableIndex) = do
        when (methodReturnType /= IVoid) $
            loadVar !getVariableTypes methodReturnType methodReturnType resultVariableIndex
        asmReturn methodReturnType
        LabelStart methodEndLabel
        updateScopeEndLabel scopeIndex methodEndLabel

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
