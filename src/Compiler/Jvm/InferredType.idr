module Compiler.Jvm.InferredType

%access public export

data InferredType = IBool | IByte | IChar | IShort | IInt | ILong | IFloat | IDouble | IRef String
                  | IArray InferredType | IUnknown

inferredObjectType : InferredType
inferredObjectType = IRef "java/lang/Object"

inferredBigIntegerType : InferredType
inferredBigIntegerType = IRef "java/math/BigInteger"

inferredStringType : InferredType
inferredStringType = IRef "java/lang/String"

inferredLambdaType : InferredType
inferredLambdaType = IRef "java/util/function/Function"

Eq InferredType where
  IBool == IBool = True
  IByte == IByte = True
  IChar == IChar = True
  IShort == IShort = True
  IInt == IInt = True
  ILong == ILong = True
  IFloat == IFloat = True
  IDouble == IDouble = True
  (Ref ty1) == (Ref ty2) = ty1 == ty2
  (IArray elemTy1) == (IArray elemTy2) = elemTy1 == elemTy2
  IUnknown == IUnknown = True
  _ == _ = False

Show InferredType where
    show IBool = "boolean"
    show IByte = "byte"
    show IChar = "char"
    show IShort = "short"
    show IInt = "int"
    show ILong = "long"
    show IFloat = "float"
    show IDouble = "double"
    show (Ref clsName) = clsName
    show (IArray elemTy) = "Array " ++ show elemTy
    show IUnknown = "unknown"

Semigroup InferredType where
  ty1 <+> ty2 = if ty1 == ty2 then ty1 else inferredObjectType

Monoid InferredType where
  neutral = IUnknown

isPrimitive : InferredType -> Bool
isPrimitive IBool = True
isPrimitive IByte = True
isPrimitive IChar = True
isPrimitive IShort = True
isPrimitive IInt = True
isPrimitive ILong = True
isPrimitive IFloat = True
isPrimitive IDouble = True
isPrimitive _ = False

InferredVariables : Type
InferredVariables = SortedMap Nat InferredType

record InferredFunctionType where
    constructor MkInferredFunctionType
    returnType : InferredType
    variablesType : InferredVariables

InferredFunctionTypes : Type
InferredFunctionTypes = SortedMap Jname InferredFunctionType
