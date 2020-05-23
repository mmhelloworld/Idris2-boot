module Compiler.Jvm.Asm

import Compiler.Jvm.Jname
import Compiler.Jvm.Jvar
import Compiler.Jvm.TypeDescriptor
import Compiler.Jvm.Annotation
import Compiler.Jvm.InferredType

import IdrisJvm.IO

%access public export

data ClassOpts = ComputeMaxs | ComputeFrames

data InvocType = InvokeInterface | InvokeSpecial | InvokeStatic | InvokeVirtual

data FieldInsType = FGetStatic | FPutStatic | FGetField | FPutField

data FrameType = FFull | FSame | FAppend

data Access = Private | Public | Static | Synthetic | Final

Eq Access where
    Private == Private = True
    Public == Public = True
    Static == Static = True
    Synthetic == Synthetic = True
    Final == Final = True
    _ == _ = False

data HandleTag = HGetField
                 | HGetStatic
                 | HPutField
                 | HPutStatic
                 | HInvokeVirtual
                 | HInvokeStatic
                 | HInvokeSpecial
                 | HNewInvokeSpecial
                 | HInvokeInterface

record Handle where
    constructor MkHandle
    tag : HandleTag
    hClassName  : String
    hMethodName : String
    hDescriptor : String
    isInterface : Bool

mutual
    asmRefTyDesc : ReferenceTypeDescriptor -> String
    asmRefTyDesc (ClassDesc c)       = "L" ++ c ++ ";"
    asmRefTyDesc (IdrisExportDesc c) = "L" ++ c ++ ";"
    asmRefTyDesc (InterfaceDesc c)   = "L" ++ c ++ ";"
    asmRefTyDesc (ArrayDesc ty)   = "[" ++ asmFieldTypeDesc ty

    refTyClassName : ReferenceTypeDescriptor -> String
    refTyClassName (ClassDesc c)       = c
    refTyClassName (InterfaceDesc c)   = c
    refTyClassName (IdrisExportDesc c) = c
    refTyClassName arr@(ArrayDesc _)   = asmRefTyDesc arr

    asmFieldTypeDesc : FieldTypeDescriptor -> String
    asmFieldTypeDesc FieldTyDescByte           = "B"
    asmFieldTypeDesc FieldTyDescChar           = "C"
    asmFieldTypeDesc FieldTyDescShort          = "S"
    asmFieldTypeDesc FieldTyDescBoolean        = "Z"
    asmFieldTypeDesc FieldTyDescDouble         = "D"
    asmFieldTypeDesc FieldTyDescFloat          = "F"
    asmFieldTypeDesc FieldTyDescInt            = "I"
    asmFieldTypeDesc FieldTyDescLong           = "J"
    asmFieldTypeDesc (FieldTyDescReference f)  = asmRefTyDesc f

asmTypeDesc : TypeDescriptor -> String
asmTypeDesc (FieldDescriptor t) = asmFieldTypeDesc t
asmTypeDesc VoidDescriptor      = "V"
asmTypeDesc (ThrowableDescriptor tyDesc) = asmTypeDesc tyDesc

data MethodDescriptor = MkMethodDescriptor (List FieldTypeDescriptor) TypeDescriptor

asmMethodDesc : MethodDescriptor -> String
asmMethodDesc (MkMethodDescriptor args returns) = "(" ++ asmArgs ++ ")" ++ r where
  asmArgs = concat $ asmFieldTypeDesc <$> args
  r = asmTypeDesc returns

data Asm : Type -> Type where
    Aaload : Asm ()
    Aastore : Asm ()
    Aconstnull : Asm ()
    Aload : Int -> Asm ()
    Anewarray : String -> Asm ()

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
    Checkcast : String -> Asm ()
    ClassCodeStart : Int -> Access -> String -> (Maybe String) -> String -> List String -> List Annotation -> Asm ()
    ClassCodeEnd : String -> Asm ()
    CreateClass : ClassOpts -> Asm ()
    CreateField : List Access -> String -> String -> String -> Maybe String -> Maybe FieldInitialValue -> Asm ()
    CreateLabel : String -> Asm String
    CreateMethod : List Access -> String -> String -> String -> Maybe String ->
                   Maybe (List String) -> List Annotation -> List (List Annotation) -> Asm ()
    D2i : Asm ()
    D2f : Asm ()
    Dadd : Asm ()
    Daload : Asm ()
    Dastore : Asm ()
    Dconst : Double -> Asm ()
    Ddiv : Asm ()
    Debug : String -> Asm ()
    Dload : Int -> Asm ()
    Dmul : Asm ()
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
    Field : FieldInsType -> String -> String -> String -> Asm ()
    FieldEnd : Asm ()
    Fload : Int -> Asm ()
    Frame : FrameType -> Nat -> (List String) -> Nat -> (List String) -> Asm ()
    FreshIfIndex : Asm Nat
    FreshLambdaIndex : String -> Asm Nat
    FreshSwitchIndex : Asm Nat
    Freturn : Asm ()
    Fstore : Int -> Asm ()
    GetFunctionName : Asm Jname
    GetFunctionLocTypes : Asm InferredVariables
    GetFunctionRetType : Asm InferredType
    GetFunctionTypes : Asm (SortedMap Jname InferredFunctionType)
    GetLocalVarCount : Asm Nat
    Goto : String -> Asm ()
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
    Ifeq : String -> Asm ()
    Ificmpge : String -> Asm ()
    Ificmpgt : String -> Asm ()
    Ificmple : String -> Asm ()
    Ificmplt : String -> Asm ()
    Ifnonnull : String -> Asm ()
    Ifnull : String -> Asm ()
    Iload : Int -> Asm ()
    Imul : Asm ()
    InstanceOf : String -> Asm ()
    InvokeMethod : InvocType -> String -> String -> String -> Bool -> Asm ()
    InvokeDynamic : String -> String -> Handle -> List BsmArg -> Asm ()
    Irem : Asm ()
    Ireturn : Asm ()
    Ishl : Asm ()
    Ishr : Asm ()
    Istore : Int -> Asm ()
    Isub : Asm ()
    Iushr : Asm ()
    L2i : Asm ()
    LabelStart : String -> Asm ()
    Ladd : Asm ()
    Laload : Asm ()
    Land : Asm ()
    Lastore : Asm ()
    Lor : Asm ()
    Lxor : Asm ()
    Lcompl : Asm ()
    Lconst : Bits64 -> Asm ()
    Ldc : Constant -> Asm ()
    Ldiv : Asm ()
    Lload : Int  -> Asm ()
    Lmul : Asm ()
    LookupSwitch : String -> List String -> List Int-> Asm ()
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
    Multianewarray : String -> Nat -> Asm ()
    New : String -> Asm ()
    Pop : Asm ()
    Pop2 : Asm ()
    Return : Asm ()
    Saload : Asm ()
    Sastore : Asm ()
    ShouldDescribeFrame : Asm Bool
    SourceInfo : String -> Asm ()
    Subroutine : Asm () -> Asm ()
    UpdateFunctionName : Jname -> Asm ()
    UpdateFunctionLocTypes : InferredVariables -> Asm ()
    UpdateFunctionRetType : InferredType -> Asm ()
    UpdateFunctionTypes : SortedMap Jname InferredFunctionType -> Asm ()
    UpdateLocalVarCount : Nat -> Asm ()
    UpdateShouldDescribeFrame : Bool -> Asm ()
    UpdateSwitchIndex : Nat -> Asm ()
    UpdateIfIndex : Nat -> Asm ()

    Pure : ty -> Asm ty
    Bind : Asm a -> (a -> Asm b) -> Asm b

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

updateLocalVarType : Nat -> InferredType -> Asm ()
updateLocalVarType index ty = do
    localTypes <- GetFunctionLocTypes
    mergedTy = maybe ty (\existingTy => if existingTy == ty then ty then inferredObjectType) $
                SortedMap.lookup index localTypes
    UpdateFunctionLocTypes $ SortedMap.insert index mergedTy localTypes

namespace Assembler

    AssemblerClass : JVM_NativeTy
    AssemblerClass = Class "io/github/mmhelloworld/idris2/jvmassembler/Assembler"

    Assembler : Type
    Assembler = JVM_Native AssemblerClass
