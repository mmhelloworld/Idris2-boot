module Compiler.Jvm.Asm

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.SortedMap
import Data.Vect

import Compiler.Jvm.InferredType
import Compiler.Jvm.Jname
import Compiler.Jvm.Jvar
import Compiler.Jvm.ShowUtil

import IdrisJvm.System
import IdrisJvm.IO
import Java.Lang
import Java.Util

%access public export

Assembler : Type
Assembler = JVM_Native (Class "io/github/mmhelloworld/idris2boot/jvmassembler/Assembler")

runtimeClass : String
runtimeClass = getRuntimeClass "Runtime"

RuntimeClass : JVM_NativeTy
RuntimeClass = Class runtimeClass

record TailCallCategory where
    constructor MkTailCallCategory

    -- Self tail calls are eliminated using JVM's GOTO
    hasSelfTailCall : Bool

    -- Non self tails calls are trampolined using INVOKEDYNAMIC
    hasNonSelfTailCall : Bool

Show TailCallCategory where
    show tailCallCategory = showType "TailCallCategory" [
        ("hasSelfTailCall", show $ hasSelfTailCall tailCallCategory),
        ("hasNonSelfTailCall", show $ hasNonSelfTailCall tailCallCategory)
    ]

ConstructorId : Type
ConstructorId = (String, Int) -- name and Idris tag

comparing : Ord a => (b -> a) -> b -> b -> Ordering
comparing p x y = compare (p x) (p y)

record Scope where
    constructor MkScope
    index : Int
    parentIndex : Maybe Int
    variableTypes : SortedMap String InferredType
    variableIndices : SortedMap String Int
    returnType : InferredType
    nextVariableIndex : Int
    lineNumbers : (Int, Int)
    labels : (String, String)
    childIndices : List Int

public export
record InferredFunctionType where
    constructor MkInferredFunctionType
    returnType : InferredType
    parameterTypes : List InferredType

record Function where
    constructor MkFunction
    idrisName : Jname
    inferredFunctionType : InferredFunctionType
    scopes : SortedMap Int Scope
    dynamicVariableCounter : Int
    jvmClassMethodName : Jname
    tailCallCategory : TailCallCategory
    optimizedBody : NamedCExp

public export
record AsmState where
    constructor MkAsmState
    functions :  SortedMap Jname Function
    currentIdrisFunction : Function
    currentMethodName : Jname
    currentScopeIndex : Int
    scopeCounter : Int
    labelCounter : Int
    lambdaCounter : Int
    lineNumberLabels : SortedMap Int String
    assembler : Assembler

data Access = Private | Public | Static | Synthetic | Final
Show Access where
    show Private = "Private"
    show Public = "Public"
    show Static = "Static"
    show Synthetic = "Synthetic"
    show Final = "Final"

data FieldInstructionType = GetStatic | PutStatic | GetField | PutField
data FrameType = Full | Same | Append
data Constant = DoubleConst Double
              | IntegerConst Int
              | LongConst Bits64
              | StringConst String
              | TypeConst String
data InvocationType = InvokeInterface | InvokeSpecial | InvokeStatic | InvokeVirtual
Show InvocationType where
    show InvokeInterface = "InvokeInterface"
    show InvokeSpecial = "InvokeSpecial"
    show InvokeStatic = "InvokeStatic"
    show InvokeVirtual = "InvokeVirtual"

data ClassOpts = ComputeMaxs | ComputeFrames
Show ClassOpts where
    show ComputeMaxs = "ComputeMaxs"
    show ComputeFrames = "ComputeFrames"

namespace HandleTag
    data HandleTag = GetField
                   | GetStatic
                   | PutField
                   | PutStatic
                   | InvokeVirtual
                   | InvokeStatic
                   | InvokeSpecial
                   | NewInvokeSpecial
                   | InvokeInterface

record Handle where
    constructor MkHandle
    tag : HandleTag
    className  : String
    methodName : String
    descriptor : String
    isInterface : Bool

data BsmArg = BsmArgGetType String | BsmArgHandle Handle

data FieldInitialValue = IntField Int | StringField String | DoubleField Double

mutual
    data AnnotationValue = AnnInt Int
                         | AnnBoolean Bool
                         | AnnByte Bits8
                         | AnnChar Char
                         | AnnShort Bits16
                         | AnnLong Bits64
                         | AnnFloat Double
                         | AnnDouble Double
                         | AnnString String
                         | AnnClass String
                         | AnnEnum String String
                         | AnnArray (List Asm.AnnotationValue)
                         | AnnAnnotation Asm.Annotation

    AnnotationProperty : Type
    AnnotationProperty = (String, Asm.AnnotationValue)

    data Annotation = MkAnnotation String (List AnnotationProperty)

data Asm : Type -> Type where
    Aaload : Asm ()
    Aastore : Asm ()
    Aconstnull : Asm ()
    Aload : Int -> Asm ()
    Anewarray : (descriptor: String) -> Asm ()

    Anewbooleanarray : Asm ()
    Anewbytearray : Asm ()
    Anewchararray : Asm ()
    Anewshortarray : Asm ()
    Anewintarray : Asm ()
    Anewlongarray : Asm ()
    Anewfloatarray : Asm ()
    Anewdoublearray : Asm ()

    Arraylength : Asm ()
    Areturn : Asm ()
    Astore : Int -> Asm ()
    Baload : Asm ()
    Bastore : Asm ()
    Caload : Asm ()
    Castore : Asm ()
    Checkcast : (descriptor: String) -> Asm ()
    ClassCodeStart : Int -> Access -> (className: String) -> (signature: Maybe String) -> (parentClassName: String) ->
                        (interfaces: List String) -> List Asm.Annotation -> Asm ()
    ClassCodeEnd : String -> Asm ()
    CreateClass : ClassOpts -> Asm ()
    CreateField : List Access -> (className: String) -> (fieldName: String) -> (descriptor: String) ->
                    (signature: Maybe String) -> Maybe FieldInitialValue -> Asm ()
    CreateLabel : String -> Asm String
    CreateMethod : List Access -> (sourceFileName: String) -> (className: String) ->
                    (methodName: String) -> (descriptor: String) ->
                    (signature: Maybe String) -> (exceptions: Maybe (List String)) ->
                    (annotations: List Asm.Annotation) ->
                    (parameterAnnotations: List (List Asm.Annotation)) -> Asm ()
    CreateIdrisConstructorClass : String -> Bool -> Int -> Asm ()
    D2i : Asm ()
    D2f : Asm ()
    Dadd : Asm ()
    Daload : Asm ()
    Dastore : Asm ()
    Dcmpg : Asm ()
    Dcmpl : Asm ()
    Dconst : Double -> Asm ()
    Ddiv : Asm ()
    Debug : String -> Asm ()
    Dload : Int -> Asm ()
    Dmul : Asm ()
    Dneg : Asm ()
    Drem : Asm ()
    Dreturn : Asm ()
    Dstore : Int -> Asm ()
    Dsub : Asm ()
    Dup : Asm ()
    Error : String -> Asm ()
    F2d : Asm ()
    Faload : Asm ()
    Fastore : Asm ()
    Fconst : Double -> Asm ()
    Field : FieldInstructionType -> (className: String) -> (fieldName: String) -> (descriptor: String) -> Asm ()
    FieldEnd : Asm ()
    Fload : Int -> Asm ()
    Frame : FrameType -> Int -> (signatures: List String) -> Int -> (signatures: List String) -> Asm ()
    Freturn : Asm ()
    Fstore : Int -> Asm ()
    Goto : (label: String) -> Asm ()
    I2b : Asm ()
    I2c : Asm ()
    I2d : Asm ()
    I2l : Asm ()
    I2s : Asm ()
    Iadd : Asm ()
    Iaload : Asm ()
    Iand : Asm ()
    Iastore : Asm ()
    Ior : Asm ()
    Ixor : Asm ()
    Icompl : Asm ()
    Iconst : Int -> Asm ()
    Idiv : Asm ()
    Ifeq : (label: String) -> Asm ()
    Ifge : (label: String) -> Asm ()
    Ifgt : (label: String) -> Asm ()
    Ificmpge : (label: String) -> Asm ()
    Ificmpgt : (label: String) -> Asm ()
    Ificmple : (label: String) -> Asm ()
    Ificmplt : (label: String) -> Asm ()
    Ificmpeq : (label: String) -> Asm ()
    Ificmpne : (label: String) -> Asm ()
    Ifle : (label: String) -> Asm ()
    Iflt : (label: String) -> Asm ()
    Ifne : (label: String) -> Asm ()
    Ifnonnull : (label: String) -> Asm ()
    Ifnull : (label: String) -> Asm ()
    Iload : Int -> Asm ()
    Imul : Asm ()
    Ineg : Asm ()
    InstanceOf : (className: String) -> Asm ()
    InvokeMethod : InvocationType -> (className: String) -> (methodName: String) -> (descriptor: String)
                    -> Bool -> Asm ()
    InvokeDynamic : (methodName: String) -> (descriptor: String) -> Handle -> List BsmArg -> Asm ()
    Irem : Asm ()
    Ireturn : Asm ()
    Ishl : Asm ()
    Ishr : Asm ()
    Istore : Int -> Asm ()
    Isub : Asm ()
    Iushr : Asm ()
    L2i : Asm ()
    LabelStart : (label: String) -> Asm ()
    Ladd : Asm ()
    Laload : Asm ()
    Land : Asm ()
    Lastore : Asm ()
    Lor : Asm ()
    Lxor : Asm ()
    Lcompl : Asm ()
    Lconst : Bits64 -> Asm ()
    Ldc : Asm.Constant -> Asm ()
    Ldiv : Asm ()
    LineNumber : Int -> String -> Asm ()
    Lload : Int  -> Asm ()
    Lmul : Asm ()
    LocalVariable : (name: String) -> (descriptor: String) -> (signature: Maybe String) -> (startLabel: String) ->
                        (endLabel: String) -> (index: Int) -> Asm ()
    LookupSwitch : (defaultLabel: String) -> (labels: List String) -> (cases: List Int) -> Asm ()
    Lrem : Asm ()
    Lreturn : Asm ()
    Lshl : Asm ()
    Lshr : Asm ()
    Lstore : Int -> Asm ()
    Lsub : Asm ()
    Lushr : Asm ()
    MaxStackAndLocal : Int -> Int -> Asm ()
    MethodCodeStart : Asm ()
    MethodCodeEnd : Asm ()
    Multianewarray : (descriptor: String) -> Int -> Asm ()
    New : (className: String) -> Asm ()
    Pop : Asm ()
    Pop2 : Asm ()
    Return : Asm ()
    Saload : Asm ()
    Sastore : Asm ()
    SourceInfo : (sourceFileName: String) -> Asm ()
    LiftIo : JVM_IO a -> Asm a

    Throw : FC -> String -> Asm a
    GetState : Asm AsmState
    SetState : AsmState -> Asm ()

    Pure : ty -> Asm ty
    Bind : Asm a -> (a -> Asm b) -> Asm b    
    
Show Scope where
    show scope = showType "Scope" [
        ("index", show $ index scope),
        ("parentIndex", show $ parentIndex scope),
        ("variableTypes", show $ variableTypes scope),
        ("variableIndices", show $ variableIndices scope),
        ("nextVariableIndex", show $ nextVariableIndex scope),
        ("lineNumbers", show $ lineNumbers scope),
        ("labels", show $ labels scope),
        ("returnType", show $ returnType scope),
        ("nextVariableIndex", show $ nextVariableIndex scope),
        ("childIndices", show $ childIndices scope)
    ]

Show InferredFunctionType where
    show inferredFunctionType = showType "InferredFunctionType" [
        ("returnType", show $ returnType inferredFunctionType),
        ("parameterTypes", show $ parameterTypes inferredFunctionType)
    ]

Show Function where
    show function = 
        showType "Function" [
            ("idrisName", show $ idrisName function),
            ("inferredFunctionType", show $ inferredFunctionType function),
            ("scopes", show $ scopes function),
            ("jvmClassMethodName", show $ jvmClassMethodName function),
            ("tailCallCategory", show $ tailCallCategory function),
            ("optimizedBody", show $ optimizedBody function)
        ]
    
Show AsmState where
    show asmState = showType "AsmState" [
        ("functions", show $ functions asmState),
        ("currentIdrisFunction", show $ currentIdrisFunction asmState),
        ("currentMethodName", show $ currentMethodName asmState),
        ("currentScopeIndex", show $ currentScopeIndex asmState),
        ("scopeCounter", show $ scopeCounter asmState),
        ("labelCounter", show $ labelCounter asmState),
        ("lambdaCounter", show $ lambdaCounter asmState),
        ("lineNumberLabels", show $ lineNumberLabels asmState)
    ]

namespace AsmDo
  (>>=) : Asm a -> (a -> Asm b) -> Asm b
  (>>=) = Bind

Functor Asm where
  map f a = Bind a (\a' => Pure $ f a')

Applicative Asm where
  pure = Pure

  (<*>) f a = Bind f (\f' =>
              Bind a (\a' =>
              Pure (f' a')))

newAsmState : Core AsmState
newAsmState = do
    assembler <- coreLift $ FFI.new (JVM_IO Assembler)
    let defaultName = Jqualified "" ""
    let function = MkFunction defaultName (MkInferredFunctionType IUnknown []) SortedMap.empty
        0 defaultName (MkTailCallCategory False False) (NmCrash emptyFC "uninitialized function")
    pure $ MkAsmState SortedMap.empty function defaultName 0 0 0 0
        SortedMap.empty assembler

updateState : (AsmState -> AsmState) -> Asm ()
updateState f = SetState $ f !GetState

getAndUpdateState : (AsmState -> AsmState) -> Asm AsmState
getAndUpdateState f = do
    state <- GetState
    SetState $ f state
    Pure state

crash : String -> a
crash message = believe_me $ unsafePerformIO $ invokeStatic Asm.RuntimeClass "crash" (String -> JVM_IO Object) message

newBigInteger : String -> Asm ()
newBigInteger "0" = Field GetStatic "java/math/BigInteger" "ZERO" "Ljava/math/BigInteger;"
newBigInteger "1" = Field GetStatic "java/math/BigInteger" "ONE" "Ljava/math/BigInteger;"
newBigInteger "10" = Field GetStatic "java/math/BigInteger" "TEN" "Ljava/math/BigInteger;"
newBigInteger i = do
    New "java/math/BigInteger"
    Dup
    Ldc $ StringConst i
    InvokeMethod InvokeSpecial "java/math/BigInteger" "<init>" "(Ljava/lang/String;)V" False

findFunction : Jname -> Asm (Maybe Function)
findFunction name = do
    state <- GetState
    Pure $ SortedMap.lookup name (functions state)

getFunction : Jname -> Asm Function
getFunction name = do
    function <- findFunction name
    maybe (Throw emptyFC $ "Unknown function " ++ show name) Pure function

getCurrentFunction : Asm Function
getCurrentFunction = currentIdrisFunction <$> GetState

setCurrentFunction : Function -> Asm ()
setCurrentFunction function = updateState $ record { currentIdrisFunction = function }

getAndUpdateFunction : (Function -> Function) -> Asm Function
getAndUpdateFunction f = do
    function <- getCurrentFunction
    let newFunction = f function
    setCurrentFunction newFunction
    updateState $ record { functions $= SortedMap.insert (idrisName newFunction) newFunction }
    Pure function

updateCurrentFunction : (Function -> Function) -> Asm ()
updateCurrentFunction f = do getAndUpdateFunction f; Pure ()

getScopes : Asm (SortedMap Int Scope)
getScopes = scopes <$> getCurrentFunction

loadFunction : Jname -> Asm ()
loadFunction idrisName = do
    function <- getFunction idrisName
    updateState $ record { currentIdrisFunction = function }

getFunctionType : Jname -> Asm InferredFunctionType
getFunctionType name = inferredFunctionType <$> (getFunction name)

getFunctionParameterTypes : Jname -> Asm (List InferredType)
getFunctionParameterTypes functionName = do
    functionType <- getFunctionType functionName
    pure $ parameterTypes functionType

findFunctionType : Jname -> Asm (Maybe InferredFunctionType)
findFunctionType functionName = do
    state <- GetState
    Pure $ inferredFunctionType <$> SortedMap.lookup functionName (functions state)

getFunctionReturnType : Jname -> Asm InferredType
getFunctionReturnType functionName =  do
    state <- GetState
    Pure $ maybe IUnknown (returnType . inferredFunctionType) $ SortedMap.lookup functionName (functions state)

getCurrentScopeIndex : Asm Int
getCurrentScopeIndex = currentScopeIndex <$> GetState

updateCurrentScopeIndex : Int -> Asm ()
updateCurrentScopeIndex scopeIndex = updateState $ record {currentScopeIndex = scopeIndex}

newScopeIndex : Asm Int
newScopeIndex = scopeCounter <$> (getAndUpdateState $ record {scopeCounter $= (+1)})

newDynamicVariableIndex : Asm Int
newDynamicVariableIndex = dynamicVariableCounter <$> (getAndUpdateFunction $ record {dynamicVariableCounter $= (+1)})

resetScope : Asm ()
resetScope = updateState $
    record {
        scopeCounter = 0,
        currentScopeIndex = 0
    }

updateScope : Int -> Scope -> Asm ()
updateScope scopeIndex scope = updateCurrentFunction $ record {scopes $= SortedMap.insert scopeIndex scope}

findScope : Int -> Asm (Maybe Scope)
findScope scopeIndex = do
   scopes <- scopes <$> getCurrentFunction
   Pure $ SortedMap.lookup scopeIndex scopes

getScope : Int -> Asm Scope
getScope scopeIndex = Pure $ fromMaybe (crash ("Unknown scope " ++ show scopeIndex)) !(findScope scopeIndex)

addScopeChild : Int -> Int -> Asm ()
addScopeChild parentScopeIndex childScopeIndex = do
    scope <- getScope parentScopeIndex
    updateScope parentScopeIndex $ record {childIndices $= (childScopeIndex ::)} scope

getJvmMethodNameForIdrisName : Jname -> Asm Jname
getJvmMethodNameForIdrisName idrisName = jvmClassMethodName <$> (getFunction idrisName)

findJvmMethodNameForIdrisName : Jname -> Asm (Maybe Jname)
findJvmMethodNameForIdrisName idrisName = do
    function <- findFunction idrisName
    Pure $ jvmClassMethodName <$> function

getRootMethodName : Asm Jname
getRootMethodName = jvmClassMethodName <$> getCurrentFunction

newLabel : Asm String
newLabel = do
    state <- GetState
    let label = "L" ++ show (labelCounter state)
    updateState $ record { labelCounter $= (+1) }
    Pure label

hasLabelAtLine : Int -> Asm Bool
hasLabelAtLine lineNumber = do
    state <- GetState
    Pure $ isJust $ SortedMap.lookup lineNumber (lineNumberLabels state)

addLineNumber : Int -> String -> Asm ()
addLineNumber lineNumber label = do
    hasLabel <- hasLabelAtLine lineNumber
    when (not hasLabel) $ do
        LineNumber lineNumber label
        updateState $ record { lineNumberLabels $= SortedMap.insert lineNumber label }

getLineNumberLabel : Int -> Asm String
getLineNumberLabel lineNumber = do
    state <- GetState
    case SortedMap.lookup lineNumber (lineNumberLabels state) of
        Just label => Pure label
        Nothing => do
            label <- newLabel
            updateState $ record { lineNumberLabels $= SortedMap.insert lineNumber label }
            Pure label

getClassName : Asm String
getClassName = className . currentMethodName <$> GetState

getMethodName : Asm String
getMethodName = methodName . currentMethodName <$> GetState

freshLambdaIndex : Asm Int
freshLambdaIndex = lambdaCounter <$> (getAndUpdateState $ record {lambdaCounter $= (+1)})

setScopeCounter : Int -> Asm ()
setScopeCounter scopeCounter = updateState $ record {scopeCounter = scopeCounter}

setLambdaCounter : Int -> Asm ()
setLambdaCounter lambdaCounter = updateState $ record {lambdaCounter = lambdaCounter}

updateScopeStartLabel : Int -> String -> Asm ()
updateScopeStartLabel scopeIndex label = do
    scope <- getScope scopeIndex
    updateScope scopeIndex (record {labels $= (\(_, endLabel) => (label, endLabel))} scope)

updateScopeEndLabel : Int -> String -> Asm ()
updateScopeEndLabel scopeIndex label = do
    scope <- getScope scopeIndex
    updateScope scopeIndex (record {labels $= (\(startLabel, _) => (startLabel, label))} scope)

createVariable : String -> Asm ()
createVariable var = do
    scopeIndex <- getCurrentScopeIndex
    scope <- getScope scopeIndex
    let variableIndex = nextVariableIndex scope
    updateScope scopeIndex $ record {
            variableTypes $= SortedMap.insert var IUnknown,
            variableIndices $= SortedMap.insert var variableIndex,
            nextVariableIndex $= (+1)
        } scope

generateVariable : (prefix : String) -> Asm String
generateVariable prefix = do
    dynamicVariableIndex <- newDynamicVariableIndex
    let variableName = prefix ++ show dynamicVariableIndex
    createVariable variableName
    Pure variableName

getVariableIndicesByName : Int -> Asm (SortedMap String Int)
getVariableIndicesByName scopeIndex = go SortedMap.empty scopeIndex
  where
    go : SortedMap String Int -> Int -> Asm (SortedMap String Int)
    go acc scopeIndex = do
        scope <- getScope scopeIndex
        let parentScopeIndex = parentIndex scope
        let scopeVariables = filter (\(var, _) => not . isJust $ SortedMap.lookup var acc) $
            SortedMap.toList $ variableIndices scope
        let variables = SortedMap.insertFrom scopeVariables acc
        maybe (Pure variables) (go variables) parentScopeIndex

getVariables : Int -> Asm (List String)
getVariables scopeIndex = do
    variableIndicesByName <-getVariableIndicesByName scopeIndex
    Pure (fst <$> sortBy comparingVariableIndices (SortedMap.toList variableIndicesByName))
  where
    comparingVariableIndices : (String, Int) -> (String, Int) -> Ordering
    comparingVariableIndices (_, index1) (_, index2) = compare index1 index2

getVariableIndexAtScope : Int -> String -> Asm Int
getVariableIndexAtScope currentScopeIndex name = go currentScopeIndex where
    go : Int -> Asm Int
    go scopeIndex = do
        scope <- getScope scopeIndex
        case SortedMap.lookup name $ variableIndices scope of
            Just index => pure index
            Nothing => case parentIndex scope of
                Just parentScopeIndex => go parentScopeIndex
                Nothing => Throw emptyFC ("Unknown var " ++ name ++ " at index " ++ show currentScopeIndex)

getVariableIndex : String -> Asm Int
getVariableIndex name = getVariableIndexAtScope !getCurrentScopeIndex name

getVariableTypeAtScope : Int -> String -> Asm InferredType
getVariableTypeAtScope scopeIndex name = do
    scope <- getScope scopeIndex
    case SortedMap.lookup name $ variableTypes scope of
        Just ty => pure ty
        Nothing => case parentIndex scope of
            Just parentScope => getVariableTypeAtScope parentScope name
            Nothing => pure IUnknown

getVariableType : String -> Asm InferredType
getVariableType name = getVariableTypeAtScope !getCurrentScopeIndex name

getVariableTypesAtScope : Int -> Asm (SortedMap Int InferredType)
getVariableTypesAtScope scopeIndex = go SortedMap.empty !(getVariables scopeIndex) where
    go : SortedMap Int InferredType -> List String -> Asm (SortedMap Int InferredType)
    go acc [] = Pure acc
    go acc (var :: vars) = do
        varIndex <- getVariableIndexAtScope scopeIndex var
        ty <- getVariableTypeAtScope scopeIndex var
        case SortedMap.lookup varIndex acc of
            Nothing => go (SortedMap.insert varIndex ty acc) vars
            _ => go acc vars

getVariableTypes : Asm (SortedMap Int InferredType)
getVariableTypes = getVariableTypesAtScope !getCurrentScopeIndex

getVariableScope : String -> Asm Scope
getVariableScope name = go !getCurrentScopeIndex where
    go : Int -> Asm Scope
    go scopeIndex = do
        scope <- getScope scopeIndex
        case SortedMap.lookup name $ variableTypes scope of
            Just _ => Pure scope
            Nothing => case parentIndex scope of
                Just parentScopeIndex => go parentScopeIndex
                Nothing => Throw emptyFC ("Unknown variable " ++ name)

addVariableType : String -> InferredType -> Asm InferredType
addVariableType var IUnknown = Pure IUnknown
addVariableType var ty = do
    scope <- getVariableScope var
    let scopeIndex = index scope
    existingTy <- getVariableTypeAtScope scopeIndex var
    let newTy = existingTy <+> ty
    updateScope scopeIndex (record {variableTypes $= SortedMap.insert var newTy} scope)
    Pure newTy

getLambdaImplementationMethodName : String -> Asm String
getLambdaImplementationMethodName prefix = do
    let declaringMethodName = methodName !getRootMethodName
    pure $ prefix ++ "$" ++ declaringMethodName ++ "$" ++ show !freshLambdaIndex

getJvmTypeDescriptor : InferredType -> String
getJvmTypeDescriptor IByte        = "B"
getJvmTypeDescriptor IChar        = "C"
getJvmTypeDescriptor IShort       = "S"
getJvmTypeDescriptor IBool        = "Z"
getJvmTypeDescriptor IDouble      = "D"
getJvmTypeDescriptor IFloat       = "F"
getJvmTypeDescriptor IInt         = "I"
getJvmTypeDescriptor ILong        = "J"
getJvmTypeDescriptor IVoid        = "V"
getJvmTypeDescriptor IUnknown     = getJvmTypeDescriptor inferredObjectType
getJvmTypeDescriptor (IRef ty)    = "L" ++ ty ++ ";"
getJvmTypeDescriptor (IArray ty)  = "[" ++ getJvmTypeDescriptor ty

asmReturn : InferredType -> Asm ()
asmReturn IVoid    = Return
asmReturn IBool    = Ireturn
asmReturn IByte    = Ireturn
asmReturn IShort   = Ireturn
asmReturn IInt     = Ireturn
asmReturn IChar    = Ireturn
asmReturn ILong    = Lreturn
asmReturn IFloat   = Freturn
asmReturn IDouble  = Dreturn
asmReturn _        = Areturn

accessNum : Access -> Int
accessNum Final     = 16
accessNum Private   = 2
accessNum Public    = 1
accessNum Static    = 8
accessNum Synthetic = 4096

fieldInsTypeNum : FieldInstructionType -> Int
fieldInsTypeNum GetStatic = 178
fieldInsTypeNum PutStatic = 179
fieldInsTypeNum GetField  = 180
fieldInsTypeNum PutField  = 181

frameTypeNum : FrameType -> Int
frameTypeNum Full   = 0
frameTypeNum Same   = 3
frameTypeNum Append = 1

invocTypeNum : InvocationType -> Int
invocTypeNum InvokeInterface = 185
invocTypeNum InvokeSpecial   = 183
invocTypeNum InvokeStatic    = 184
invocTypeNum InvokeVirtual   = 182

handleTagOpcode : HandleTag -> Int
handleTagOpcode GetField         = 1
handleTagOpcode GetStatic        = 2
handleTagOpcode PutField         = 3
handleTagOpcode PutStatic        = 4
handleTagOpcode InvokeVirtual    = 5
handleTagOpcode InvokeStatic     = 6
handleTagOpcode InvokeSpecial    = 7
handleTagOpcode NewInvokeSpecial = 8
handleTagOpcode InvokeInterface  = 9

constantToObject : Asm.Constant -> Object
constantToObject (DoubleConst d) = believe_me $ JDouble.valueOf d
constantToObject (IntegerConst n) = believe_me $ JInteger.valueOf n
constantToObject (LongConst n) = believe_me $ Long.valueOf n
constantToObject (StringConst str) = believe_me str
constantToObject (TypeConst str) = believe_me str

assemblerClass : String -> String
assemblerClass name = "io/github/mmhelloworld/idris2boot/jvmassembler/" ++ name

JAnnotation : Type
JAnnotation = javaClass (assemblerClass "Annotation")

JAnnString : Type
JAnnString = javaClass (assemblerClass "AnnotationValue$AnnString")

JAnnEnum : Type
JAnnEnum = javaClass (assemblerClass "AnnotationValue$AnnEnum")

JAnnInt : Type
JAnnInt = javaClass (assemblerClass "AnnotationValue$AnnInt")

JAnnBoolean : Type
JAnnBoolean = javaClass (assemblerClass "AnnotationValue$AnnBoolean")

JAnnByte : Type
JAnnByte = javaClass (assemblerClass "AnnotationValue$AnnByte")

JAnnChar : Type
JAnnChar = javaClass (assemblerClass "AnnotationValue$AnnChar")

JAnnShort : Type
JAnnShort = javaClass (assemblerClass "AnnotationValue$AnnShort")

JAnnLong : Type
JAnnLong = javaClass (assemblerClass "AnnotationValue$AnnLong")

JAnnFloat : Type
JAnnFloat = javaClass (assemblerClass "AnnotationValue$AnnFloat")

JAnnDouble : Type
JAnnDouble = javaClass (assemblerClass "AnnotationValue$AnnDouble")

JAnnClass : Type
JAnnClass = javaClass (assemblerClass "AnnotationValue$AnnClass")

JAnnArray : Type
JAnnArray = javaClass (assemblerClass "AnnotationValue$AnnArray")

JAnnAnnotation : Type
JAnnAnnotation = javaClass (assemblerClass "AnnotationValue$AnnAnnotation")

JAnnotationProperty : Type
JAnnotationProperty = javaClass (assemblerClass "AnnotationProperty")

JAnnotationValue: Type
JAnnotationValue = javaClass (assemblerClass "AnnotationValue")

Inherits JAnnotationValue JAnnInt where {}
Inherits JAnnotationValue JAnnBoolean where {}
Inherits JAnnotationValue JAnnByte where {}
Inherits JAnnotationValue JAnnChar where {}
Inherits JAnnotationValue JAnnShort where {}
Inherits JAnnotationValue JAnnLong where {}
Inherits JAnnotationValue JAnnFloat where {}
Inherits JAnnotationValue JAnnDouble where {}
Inherits JAnnotationValue JAnnEnum where {}
Inherits JAnnotationValue JAnnClass where {}
Inherits JAnnotationValue JAnnAnnotation where {}

JHandle: Type
JHandle = javaClass (assemblerClass "JHandle")

JBsmArg: Type
JBsmArg = javaClass (assemblerClass "JBsmArg")

JBsmArgGetType: Type
JBsmArgGetType = javaClass (assemblerClass "JBsmArg$JBsmArgGetType")

JBsmArgHandle: Type
JBsmArgHandle = javaClass (assemblerClass "JBsmArg$JBsmArgHandle")

toJClassOpts : ClassOpts -> Int
toJClassOpts ComputeMaxs = 1
toJClassOpts ComputeFrames = 2

toJHandle : Handle -> JVM_IO JHandle
toJHandle (MkHandle tag hcname hmname hdesc hIsIntf) = do
    let tagNum = handleTagOpcode tag
    FFI.new (Int -> String -> String -> String -> Bool -> JVM_IO JHandle) tagNum hcname hmname hdesc hIsIntf

toJbsmArg : BsmArg -> JVM_IO JBsmArg
toJbsmArg (BsmArgGetType desc) = believe_me <$> FFI.new (String -> JVM_IO JBsmArgGetType) desc
toJbsmArg (BsmArgHandle handle) = do
    jhandle <- toJHandle handle
    believe_me <$> FFI.new (JHandle -> JVM_IO JBsmArgHandle) jhandle

mutual
    toJAnnotationValue : Asm.AnnotationValue -> JVM_IO JAnnotationValue
    toJAnnotationValue (AnnString s) = believe_me <$> FFI.new (String -> JVM_IO JAnnString) s
    toJAnnotationValue (AnnEnum enum s) = believe_me <$> FFI.new (String -> String -> JVM_IO JAnnEnum) enum s
    toJAnnotationValue (AnnInt n) = believe_me <$> FFI.new (Int -> JVM_IO JAnnInt) n
    toJAnnotationValue (AnnBoolean n) = believe_me <$> FFI.new (Bool -> JVM_IO JAnnBoolean) n
    toJAnnotationValue (AnnByte n) = believe_me <$> FFI.new (Bits8 -> JVM_IO JAnnByte) n
    toJAnnotationValue (AnnChar n) = believe_me <$> FFI.new (Char -> JVM_IO JAnnChar) n
    toJAnnotationValue (AnnShort n) = believe_me <$> FFI.new (Bits16 -> JVM_IO JAnnShort) n
    toJAnnotationValue (AnnLong n) = believe_me <$> FFI.new (Bits64 -> JVM_IO JAnnLong) n
    toJAnnotationValue (AnnFloat n) = believe_me <$> FFI.new (Double -> JVM_IO JAnnFloat) n
    toJAnnotationValue (AnnDouble n) = believe_me <$> FFI.new (Double -> JVM_IO JAnnDouble) n
    toJAnnotationValue (AnnClass n) = believe_me <$> FFI.new (String -> JVM_IO JAnnClass) n
    toJAnnotationValue (AnnAnnotation n) = do
        jAnn <- toJAnnotation n
        FFI.new (JAnnotation -> JVM_IO JAnnAnnotation) jAnn
    toJAnnotationValue (AnnArray values) = do
      jvalues <- ArrayList.fromList !(sequence $ toJAnnotationValue <$> values)
      believe_me <$> FFI.new (JList -> JVM_IO JAnnArray) (believe_me jvalues)

    toJAnnotationProperty : Asm.AnnotationProperty -> JVM_IO JAnnotationProperty
    toJAnnotationProperty (name, annValue) = do
      jAnnotationValue <- toJAnnotationValue annValue
      FFI.new (String -> JAnnotationValue -> JVM_IO JAnnotationProperty) name jAnnotationValue

    toJAnnotation : Asm.Annotation -> JVM_IO JAnnotation
    toJAnnotation (MkAnnotation name props) = do
      jprops <- ArrayList.fromList !(sequence $ toJAnnotationProperty <$> props)
      FFI.new (String -> JList -> JVM_IO JAnnotation) name (believe_me jprops)

toJFieldInitialValue : FieldInitialValue -> Object
toJFieldInitialValue (IntField n) = believe_me $ JInteger.valueOf n
toJFieldInitialValue (StringField s) = believe_me s
toJFieldInitialValue (DoubleField d) = believe_me $ JDouble.valueOf d

loadBigInteger : String -> Asm ()
loadBigInteger "0" = Field GetStatic "java/math/BigInteger" "ZERO" "Ljava/math/BigInteger;"
loadBigInteger "1" = Field GetStatic "java/math/BigInteger" "ONE" "Ljava/math/BigInteger;"
loadBigInteger "10" = Field GetStatic "java/math/BigInteger" "TEN" "Ljava/math/BigInteger;"
loadBigInteger i = do
    New "java/math/BigInteger"
    Dup
    Ldc $ StringConst i
    InvokeMethod InvokeSpecial "java/math/BigInteger" "<init>" "(Ljava/lang/String;)V" False
  
getMethodDescriptor :InferredFunctionType -> String
getMethodDescriptor (MkInferredFunctionType retTy []) = "()" ++ getJvmTypeDescriptor retTy
getMethodDescriptor (MkInferredFunctionType retTy argTypes) =
    let argDescs = getJvmTypeDescriptor <$> argTypes
        retTyDesc = getJvmTypeDescriptor retTy
    in "(" ++ (the String $ concat argDescs) ++ ")" ++ retTyDesc

assemble : AsmState -> JVM_IO a -> Core (a, AsmState)
assemble state m = do
  a <- coreLift m
  pure (a, state)

getIdrisFunctionName : String -> String -> String -> Jname
getIdrisFunctionName moduleName fileName idrisFunctionName =
    let name = unsafePerformIO $ invokeStatic (Class $ assemblerClass "IdrisName") "getIdrisFunctionName"
            (String -> String -> String -> JVM_IO String) moduleName fileName idrisFunctionName
        (className :: functionName :: _) = split (== ',') name
    in Jqualified className functionName

getIdrisConstructorClassName : String -> String -> String -> Jname
getIdrisConstructorClassName moduleName fileName idrisFunctionName =
    let name = unsafePerformIO $ invokeStatic (Class $ assemblerClass "IdrisName") "getIdrisConstructorClassName"
            (String -> String -> String -> JVM_IO String) moduleName fileName idrisFunctionName
    in Jqualified name ""

metafactoryDesc : String
metafactoryDesc =
  concat $ the (List String) [ "("
         , "Ljava/lang/invoke/MethodHandles$Lookup;"
         , "Ljava/lang/String;Ljava/lang/invoke/MethodType;"
         , "Ljava/lang/invoke/MethodType;"
         , "Ljava/lang/invoke/MethodHandle;"
         , "Ljava/lang/invoke/MethodType;"
         , ")"
         , "Ljava/lang/invoke/CallSite;"
         ]

invokeDynamic : (implClassName: String) -> (implMethodName: String) -> (interfaceMethodName: String) ->
                (invokeDynamicDesc: String) -> (samDesc: String) -> (implMethodDesc: String) ->
                (instantiatedMethodDesc: String) -> Asm ()
invokeDynamic implClassName implMethodName interfaceMethodName invokeDynamicDesc samDesc implMethodDesc
    instantiatedMethodDesc =
    let metafactoryHandle = MkHandle InvokeStatic "java/lang/invoke/LambdaMetafactory" "metafactory"
            metafactoryDesc False
        implMethodHandle = MkHandle InvokeStatic implClassName implMethodName implMethodDesc False
        metafactoryArgs = [ BsmArgGetType samDesc
                        , BsmArgHandle implMethodHandle
                        , BsmArgGetType instantiatedMethodDesc
                        ]
    in InvokeDynamic interfaceMethodName invokeDynamicDesc metafactoryHandle metafactoryArgs

getThunkType : InferredType -> InferredType
getThunkType IInt = intThunkType
getThunkType IDouble = doubleThunkType
getThunkType _ = thunkType

getThunkValueType : InferredType -> InferredType
getThunkValueType ty = if ty == intThunkType then IInt
    else if ty == doubleThunkType then IDouble
    else if ty == thunkType then inferredObjectType
    else ty

isThunkType : InferredType -> Bool
isThunkType ty = ty == intThunkType || ty == doubleThunkType || ty == thunkType

shouldDebugAsm : Bool
shouldDebugAsm =
    let shouldDebugProperty = unsafePerformIO $ System.getPropertyWithDefault "IDRIS_JVM_DEBUG_ASM" ""
    in shouldDebugProperty == "true"

shouldDebug : Bool
shouldDebug =
    let shouldDebugProperty = unsafePerformIO $ System.getPropertyWithDefault "IDRIS_JVM_DEBUG" ""
    in shouldDebugProperty == "true"

namespace LocalDateTime
    LocalDateTimeClass : JVM_NativeTy
    LocalDateTimeClass = Class "java/time/LocalDateTime"

    LocalDateTime : Type
    LocalDateTime = JVM_Native LocalDateTimeClass

    export
    currentTimeString : JVM_IO String
    currentTimeString = do
        now <- invokeStatic LocalDateTimeClass "now" (JVM_IO LocalDateTime)
        invokeInstance "toString" (LocalDateTime -> JVM_IO String) now

export
debug : Lazy String -> Asm ()
debug msg =
    if shouldDebug
        then do
            t <- LiftIo currentTimeString
            Debug $ t ++ ": " ++ msg
        else Pure ()

runAsm : AsmState -> Asm a -> Core (a, AsmState)
runAsm state Aaload = assemble state $ invokeInstance "aaload" (Assembler -> JVM_IO ()) (assembler state)

runAsm state Aastore = assemble state $ invokeInstance "aastore" (Assembler -> JVM_IO ()) (assembler state)

runAsm state Aconstnull = assemble state $ invokeInstance "aconstnull" (Assembler -> JVM_IO ()) (assembler state)

runAsm state (Aload n) = assemble state $
    invokeInstance "aload" (Assembler -> Int -> JVM_IO ()) (assembler state) n

runAsm state (Anewarray desc) = assemble state $
    invokeInstance "anewarray" (Assembler -> String -> JVM_IO ()) (assembler state) desc
runAsm state Anewintarray     = assemble state $
    invokeInstance "anewintarray" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Anewbooleanarray = assemble state $
    invokeInstance "anewbooleanarray" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Anewbytearray    = assemble state $
    invokeInstance "anewbytearray" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Anewchararray    = assemble state $
    invokeInstance "anewchararray" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Anewshortarray   = assemble state $
    invokeInstance "anewshortarray" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Anewlongarray    = assemble state $
    invokeInstance "anewlongarray" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Anewfloatarray   = assemble state $
    invokeInstance "anewfloatarray" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Anewdoublearray  = assemble state $
    invokeInstance "anewdoublearray" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Arraylength      = assemble state $ invokeInstance "arraylength" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Areturn          = assemble state $ invokeInstance "areturn" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Astore n)       = assemble state $
    invokeInstance "astore" (Assembler -> Int -> JVM_IO ()) (assembler state) n
runAsm state Baload           = assemble state $ invokeInstance "baload" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Bastore          = assemble state $ invokeInstance "bastore" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Caload           = assemble state $ invokeInstance "caload" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Castore          = assemble state $ invokeInstance "castore" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Checkcast desc) = assemble state $
    invokeInstance "checkcast" (Assembler -> String -> JVM_IO ()) (assembler state) desc
runAsm state (ClassCodeStart version access className sig parent intf anns) = assemble state $ do
  janns <- sequence $ toJAnnotation <$> anns
  interfaces <- ArrayList.fromList intf
  annotations <- ArrayList.fromList janns
  invokeInstance
    "classCodeStart"
    (Assembler -> Int -> Int -> (className: String) -> (signature: String) -> (className: String) -> JList -> JList ->
        JVM_IO ())
    (assembler state)
    version
    (accessNum access)
    className
    (maybeToNullableString sig)
    parent
    (believe_me interfaces)
    (believe_me annotations)

runAsm state (ClassCodeEnd out) =
    assemble state $ invokeInstance "classCodeEnd" (Assembler -> String -> JVM_IO ()) (assembler state) out
runAsm state (CreateClass opts) =
    assemble state $ invokeInstance "createClass" (Assembler -> Int -> JVM_IO ()) (assembler state) (toJClassOpts opts)
runAsm state (CreateField accs className fieldName desc sig fieldInitialValue) = assemble state $ do
  let jaccs = sum $ accessNum <$> accs
  invokeInstance
    "createField"
    (Assembler -> Int -> (className: String) -> (fieldName: String) -> (descriptor: String) ->
        (signature: String) -> Object -> JVM_IO ())
    (assembler state)
    jaccs
    className
    fieldName
    desc
    (maybeToNullableString sig)
    (maybeToNullable (toJFieldInitialValue <$> fieldInitialValue))

runAsm state (CreateLabel label) = assemble state $ do
  invokeInstance "createLabel" (Assembler -> String -> JVM_IO ()) (assembler state) label
  pure label

runAsm state (CreateMethod accs sourceFileName className methodName desc sig exceptions anns paramAnns) =
    let newState = record { currentMethodName = Jqualified className methodName } state
    in assemble newState $ do
        let jaccs = sum $ accessNum <$> accs
        jexceptions <- sequence $ ArrayList.fromList <$> exceptions
        janns <- ArrayList.fromList !(sequence $ toJAnnotation <$> anns)
        jparamAnns <- ArrayList.fromList
            !(sequence $ (\paramAnn => ArrayList.fromList !(sequence $ toJAnnotation <$> paramAnn)) <$> paramAnns)
        invokeInstance
            "createMethod"
            (Assembler -> Int -> (sourceFileName: String) -> (className: String) -> (methodName: String) ->
                (descriptor: String) -> (signature: String) -> JList -> JList -> JList -> JVM_IO ())
            (assembler state)
            jaccs
            sourceFileName
            className
            methodName
            desc
            (maybeToNullableString sig)
            (maybeToNullable $ believe_me jexceptions)
            (believe_me janns)
            (believe_me jparamAnns)

runAsm state (CreateIdrisConstructorClass className isStringConstructor constructorParameterCount) =
    assemble state $ invokeInstance "createIdrisConstructorClass" (Assembler -> String -> Bool -> Int -> JVM_IO ())
        (assembler state) className isStringConstructor constructorParameterCount

runAsm state D2i = assemble state $ invokeInstance "d2i" (Assembler -> JVM_IO ()) (assembler state)
runAsm state D2f = assemble state $ invokeInstance "d2f" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Dadd = assemble state $ invokeInstance "dadd" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Dcmpg = assemble state $ invokeInstance "dcmpg" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Dcmpl = assemble state $ invokeInstance "dcmpl" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Dconst n) =
    assemble state $ invokeInstance "dconst" (Assembler -> Double -> JVM_IO ()) (assembler state) n
runAsm state Daload = assemble state $ invokeInstance "daload" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Dastore = assemble state $ invokeInstance "dastore" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Ddiv = assemble state $ invokeInstance "ddiv" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Debug message) =
    assemble state $ invokeInstance "debug" (Assembler -> String -> JVM_IO ()) (assembler state) message
runAsm state (Dload n) =
    assemble state $ invokeInstance "dload" (Assembler -> Int -> JVM_IO ()) (assembler state) n
runAsm state Dmul = assemble state $ invokeInstance "dmul" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Dneg = assemble state $ invokeInstance "dneg" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Drem = assemble state $ invokeInstance "drem" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Dreturn = assemble state $ invokeInstance "dreturn" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Dstore n) =
    assemble state $ invokeInstance "dstore" (Assembler -> Int -> JVM_IO ()) (assembler state) n
runAsm state Dsub = assemble state $ invokeInstance "dsub" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Dup = assemble state $ invokeInstance "dup" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Error err) =
    assemble state $ invokeInstance "error" (Assembler -> String -> JVM_IO ()) (assembler state) err
runAsm state F2d = assemble state $ invokeInstance "f2d" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Faload = assemble state $ invokeInstance "faload" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Fastore = assemble state $ invokeInstance "fastore" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Fconst n) =
    assemble state $ invokeInstance "fconst" (Assembler -> Double -> JVM_IO ()) (assembler state) n
runAsm state (Field finsType cname fname desc) = assemble state $ do
  let finsTypeNum = fieldInsTypeNum finsType
  invokeInstance
    "field"
    (Assembler -> Int -> (className: String) -> (fieldName: String) -> (descriptor: String) -> JVM_IO ())
    (assembler state)
    finsTypeNum
    cname
    fname
    desc

runAsm state FieldEnd = assemble state $ invokeInstance "fieldEnd" (Assembler -> JVM_IO ()) (assembler state)

runAsm state (Fload n) =
    assemble state $ invokeInstance "fload" (Assembler -> Int -> JVM_IO ()) (assembler state) n

runAsm state (Frame frameType nLocal localSigs nStack stackSigs) = assemble state $ do
  let ftypeNum = frameTypeNum frameType
  jlocalSigs <- ArrayList.fromList localSigs
  jstackSigs <- ArrayList.fromList stackSigs
  invokeInstance
    "frame"
    (Assembler -> Int -> Int -> JList -> Int -> JList -> JVM_IO ())
    (assembler state)
    ftypeNum
    nLocal
    (believe_me jlocalSigs)
    nStack
    (believe_me jstackSigs)

runAsm state Freturn = assemble state $ invokeInstance "freturn" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Fstore n) =
    assemble state $ invokeInstance "fstore" (Assembler -> Int -> JVM_IO ()) (assembler state) n

runAsm state (Goto label) =
    assemble state $ invokeInstance "gotoLabel" (Assembler -> String -> JVM_IO ()) (assembler state) label

runAsm state I2b = assemble state $ invokeInstance "i2b" (Assembler -> JVM_IO ()) (assembler state)
runAsm state I2c = assemble state $ invokeInstance "i2c" (Assembler -> JVM_IO ()) (assembler state)
runAsm state I2d = assemble state $ invokeInstance "i2d" (Assembler -> JVM_IO ()) (assembler state)
runAsm state I2l = assemble state $ invokeInstance "i2l" (Assembler -> JVM_IO ()) (assembler state)
runAsm state I2s = assemble state $ invokeInstance "i2s" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Iadd = assemble state $ invokeInstance "iadd" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Iaload = assemble state $ invokeInstance "iaload" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Iand = assemble state $ invokeInstance "iand" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Iastore = assemble state $ invokeInstance "iastore" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Ior = assemble state $ invokeInstance "ior" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Ixor = assemble state $ invokeInstance "ixor" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Icompl = assemble state $ invokeInstance "icompl" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Iconst n) = assemble state $ invokeInstance "iconst" (Assembler -> Int -> JVM_IO ()) (assembler state) n
runAsm state Idiv = assemble state $ invokeInstance "idiv" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Ifeq label) =
    assemble state $ invokeInstance "ifeq" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ifge label) =
    assemble state $ invokeInstance "ifge" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ifgt label) =
    assemble state $ invokeInstance "ifgt" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ificmpge label) =
    assemble state $ invokeInstance "ificmpge" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ificmpgt label) =
    assemble state $ invokeInstance "ificmpgt" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ificmple label) =
    assemble state $ invokeInstance "ificmple" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ificmplt label) =
    assemble state $ invokeInstance "ificmplt" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ificmpeq label) =
    assemble state $ invokeInstance "ificmpeq" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ificmpne label) =
    assemble state $ invokeInstance "ificmpne" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ifle label) =
    assemble state $ invokeInstance "ifle" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Iflt label) =
    assemble state $ invokeInstance "iflt" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ifne label) =
    assemble state $ invokeInstance "ifne" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ifnonnull label) =
    assemble state $ invokeInstance "ifnonnull" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Ifnull label) =
    assemble state $ invokeInstance "ifnull" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state (Iload n) =
    assemble state $ invokeInstance "iload" (Assembler -> Int -> JVM_IO ()) (assembler state) n
runAsm state Imul = assemble state $ invokeInstance "imul" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Ineg = assemble state $ invokeInstance "ineg" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (InstanceOf className) =
    assemble state $ invokeInstance "instanceOf" (Assembler -> String -> JVM_IO ()) (assembler state) className
runAsm state (InvokeMethod invocType cname mname desc isIntf) = assemble state $ do
  let invocTypeAsm = invocTypeNum invocType
  invokeInstance
    "invokeMethod"
    (Assembler -> Int -> (className: String) -> (methodName: String) -> (descriptor: String) -> Bool -> JVM_IO ())
    (assembler state)
    invocTypeAsm
    cname
    mname
    desc
    isIntf

runAsm state (InvokeDynamic mname desc handle bsmArgs) = assemble state $ do
  jbsmArgsList <- sequence $ toJbsmArg <$> bsmArgs
  jbsmArgs <- ArrayList.fromList jbsmArgsList
  jhandle <- toJHandle handle
  invokeInstance
    "invokeDynamic"
    (Assembler -> (methodName: String) -> (descriptor: String) -> JHandle -> JList -> JVM_IO ())
    (assembler state)
    mname
    desc
    jhandle
    (believe_me jbsmArgs)

runAsm state Irem = assemble state $ invokeInstance "irem" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Ireturn = assemble state $ invokeInstance "ireturn" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Ishl = assemble state $ invokeInstance "ishl" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Ishr = assemble state $ invokeInstance "ishr" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Istore n) = assemble state $
    invokeInstance "istore" (Assembler -> Int -> JVM_IO ()) (assembler state) n
runAsm state Isub = assemble state $ invokeInstance "isub" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Iushr = assemble state $ invokeInstance "iushr" (Assembler -> JVM_IO ()) (assembler state)
runAsm state L2i = assemble state $ invokeInstance "l2i" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (LabelStart label) =
    assemble state $ invokeInstance "labelStart" (Assembler -> String -> JVM_IO ()) (assembler state) label
runAsm state Ladd = assemble state $ invokeInstance "ladd" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Land = assemble state $ invokeInstance "land" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Laload = assemble state $ invokeInstance "laload" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Lastore = assemble state $ invokeInstance "lastore" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Lor = assemble state $ invokeInstance "lor" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Lxor = assemble state $ invokeInstance "lxor" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Lcompl = assemble state $ invokeInstance "lcompl" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Lconst c) = assemble state $
    invokeInstance "lconst" (Assembler -> Bits64 -> JVM_IO ()) (assembler state) c

runAsm state (Ldc (TypeConst ty)) =
    assemble state $ invokeInstance "ldcType" (Assembler -> String -> JVM_IO ()) (assembler state) ty
runAsm state (Ldc constant) = assemble state $
    invokeInstance "ldc" (Assembler -> Object -> JVM_IO ()) (assembler state) (constantToObject constant)

runAsm state Ldiv = assemble state $ invokeInstance "ldiv" (Assembler -> JVM_IO ()) (assembler state)

runAsm state (LineNumber lineNumber label) = assemble state $
    invokeInstance "lineNumber" (Assembler -> Int -> String -> JVM_IO ()) (assembler state) lineNumber label

runAsm state (Lload n) = assemble state $
    invokeInstance "lload" (Assembler -> Int -> JVM_IO ()) (assembler state) n
runAsm state Lmul = assemble state $ invokeInstance "lmul" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (LookupSwitch defaultLabel labels cases) = assemble state $ do
  jlabels <- ArrayList.fromList labels
  jcases <- ArrayList.fromList $ JInteger.valueOf <$> cases
  invokeInstance
    "lookupSwitch"
    (Assembler -> String -> JList -> JList -> JVM_IO ())
    (assembler state)
    defaultLabel
    (believe_me jlabels)
    (believe_me jcases)

runAsm state (LocalVariable name descriptor signature startLabel endLabel index) = assemble state $
    invokeInstance
        "localVariable"
        (Assembler -> String -> String -> String -> String -> String -> Int -> JVM_IO ())
        (assembler state)
        name
        descriptor
        (maybeToNullableString signature)
        startLabel
        endLabel
        index

runAsm state Lrem = assemble state $ invokeInstance "lrem" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Lreturn = assemble state $ invokeInstance "lreturn" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Lshl = assemble state $ invokeInstance "lshl" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Lshr = assemble state $ invokeInstance "lshr" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Lstore n) = assemble state $
    invokeInstance "lstore" (Assembler -> Int -> JVM_IO ()) (assembler state) n
runAsm state Lsub = assemble state $ invokeInstance "lsub" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Lushr = assemble state $ invokeInstance "lushr" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (MaxStackAndLocal stack local) = assemble state $
    invokeInstance "maxStackAndLocal" (Assembler -> Int -> Int -> JVM_IO ()) (assembler state) stack local
runAsm state MethodCodeStart = assemble state $
    invokeInstance "methodCodeStart" (Assembler -> JVM_IO ()) (assembler state)
runAsm state MethodCodeEnd = assemble state $ invokeInstance "methodCodeEnd" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (Multianewarray desc dims) = assemble state $
    invokeInstance "multiANewArray" (Assembler -> String -> Int -> JVM_IO ()) (assembler state) desc dims
runAsm state (New cname) = assemble state $
    invokeInstance "asmNew" (Assembler -> String -> JVM_IO ()) (assembler state) cname
runAsm state Pop = assemble state $ invokeInstance "pop" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Pop2 = assemble state $ invokeInstance "pop2" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Return = assemble state $ invokeInstance "voidReturn" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Saload = assemble state $ invokeInstance "saload" (Assembler -> JVM_IO ()) (assembler state)
runAsm state Sastore = assemble state $ invokeInstance "sastore" (Assembler -> JVM_IO ()) (assembler state)
runAsm state (SourceInfo sourceFileName)
  = assemble state $ invokeInstance "sourceInfo" (Assembler -> String -> JVM_IO ()) (assembler state) sourceFileName
runAsm state (LiftIo action) = assemble state action

runAsm state (Throw fc message) = pure (crash $ show fc ++ ": " ++ message, state)
runAsm state GetState = pure (state, state)
runAsm state (SetState newState) = pure ((), newState)

runAsm st (Pure value) = pure (value, st)
runAsm st (Bind action f) = do
  (result, nextSt) <- runAsm st action
  runAsm nextSt $ f result