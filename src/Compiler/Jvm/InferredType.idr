module Compiler.Jvm.InferredType

%access public export

data InferredType = IBool | IByte | IChar | IShort | IInt | ILong | IFloat | IDouble | IRef String
                  | IArray InferredType | IVoid | IUnknown

Eq InferredType where
  IBool == IBool = True
  IByte == IByte = True
  IChar == IChar = True
  IShort == IShort = True
  IInt == IInt = True
  ILong == ILong = True
  IFloat == IFloat = True
  IDouble == IDouble = True
  (IRef ty1) == (IRef ty2) = ty1 == ty2
  (IArray elemTy1) == (IArray elemTy2) = elemTy1 == elemTy2
  IUnknown == IUnknown = True
  IVoid == IVoid = True
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
    show (IRef clsName) = clsName
    show (IArray elemTy) = "Array " ++ show elemTy
    show IUnknown = "unknown"
    show IVoid = "void"

inferredObjectType : InferredType
inferredObjectType = IRef "java/lang/Object"

bigIntegerClass : String
bigIntegerClass = "java/math/BigInteger"

inferredBigIntegerType : InferredType
inferredBigIntegerType = IRef bigIntegerClass

stringClass : String
stringClass = "java/lang/String"

inferredStringType : InferredType
inferredStringType = IRef stringClass

inferredLambdaType : InferredType
inferredLambdaType = IRef "java/util/function/Function"

arrayListClass : String
arrayListClass = "java/util/ArrayList"

arrayListType : InferredType
arrayListType = IRef arrayListClass

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

getRuntimeClass : String -> String
getRuntimeClass name = "io/github/mmhelloworld/idris2boot/runtime/" ++ name

intThunkClass : String
intThunkClass = getRuntimeClass "IntThunk"

doubleThunkClass : String
doubleThunkClass = getRuntimeClass "DoubleThunk"

thunkClass : String
thunkClass = getRuntimeClass "Thunk"

intThunkType : InferredType
intThunkType = IRef intThunkClass

doubleThunkType : InferredType
doubleThunkType = IRef doubleThunkClass

thunkType : InferredType
thunkType = IRef thunkClass

delayedClass : String
delayedClass = getRuntimeClass "Delayed"

delayedType : InferredType
delayedType = IRef delayedClass

idrisObjectClass : String
idrisObjectClass = getRuntimeClass "IdrisObject"

arraysClass : String
arraysClass = getRuntimeClass "Arrays"

idrisObjectType : InferredType
idrisObjectType = IRef idrisObjectClass

isRefType : InferredType -> Bool
isRefType (IRef _) = True
isRefType _ = False

Semigroup InferredType where
  IUnknown <+> ty2 = ty2
  ty1 <+> IUnknown = ty1
  ty1 <+> ty2 = if ty1 == ty2 then ty1 else inferredObjectType

Monoid InferredType where
  neutral = IUnknown

parse : String -> InferredType
parse "boolean" = IBool
parse "byte" = IByte
parse "char" = IChar
parse "short" = IShort
parse "int" = IInt
parse "long" = ILong
parse "float" = IFloat
parse "double" = IDouble
parse "String" = inferredStringType
parse "BigInteger" = inferredBigIntegerType
parse "void" = IVoid
parse className = IRef className

createExtPrimTypeSpec : InferredType -> String
createExtPrimTypeSpec IBool = "Bool"
createExtPrimTypeSpec IByte = "Byte"
createExtPrimTypeSpec IShort = "Short"
createExtPrimTypeSpec IInt = "Int"
createExtPrimTypeSpec IChar = "Char"
createExtPrimTypeSpec ILong = "Long"
createExtPrimTypeSpec IFloat = "Float"
createExtPrimTypeSpec IDouble = "Double"
createExtPrimTypeSpec (IArray ty) = "[" ++ createExtPrimTypeSpec ty
createExtPrimTypeSpec IVoid = "void"
createExtPrimTypeSpec IUnknown = createExtPrimTypeSpec inferredObjectType
createExtPrimTypeSpec (IRef ty) = ty