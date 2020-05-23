module Compiler.Jvm.TypeDescriptor

%access public export

mutual

  data FieldInitialValue = IntField Int | StringField String | DoubleField Double
  data BsmArg = BsmArgGetType String | BsmArgHandle Handle

  data Constant = DoubleConst Double
                | IntegerConst Int
                | LongConst Bits64
                | StringConst String
                | TypeConst String

  data ReferenceTypeDescriptor = ClassDesc String
                               | InterfaceDesc String
                               | ArrayDesc FieldTypeDescriptor
                               | IdrisExportDesc String

  data FieldTypeDescriptor = FieldTyDescByte
                           | FieldTyDescChar
                           | FieldTyDescShort
                           | FieldTyDescBoolean
                           | FieldTyDescDouble
                           | FieldTyDescFloat
                           | FieldTyDescInt
                           | FieldTyDescLong
                           | FieldTyDescReference ReferenceTypeDescriptor

  data TypeDescriptor = FieldDescriptor FieldTypeDescriptor | VoidDescriptor | ThrowableDescriptor TypeDescriptor

  Eq ReferenceTypeDescriptor where
    (ClassDesc className1          ) == (ClassDesc className2          ) = className1 == className2
    (InterfaceDesc className1      ) == (InterfaceDesc className2      ) = className1 == className2
    (ArrayDesc elemDesc1           ) == (ArrayDesc elemDesc2           ) = elemDesc1 == elemDesc2
    (IdrisExportDesc className1    ) == (IdrisExportDesc className2    ) = className1 == className2
    _                                == _                                = False

  Eq FieldTypeDescriptor where
      FieldTyDescByte                == FieldTyDescByte               = True
      FieldTyDescChar                == FieldTyDescChar               = True
      FieldTyDescShort               == FieldTyDescShort              = True
      FieldTyDescBoolean             == FieldTyDescBoolean            = True
      FieldTyDescDouble              == FieldTyDescDouble             = True
      FieldTyDescFloat               == FieldTyDescFloat              = True
      FieldTyDescInt                 == FieldTyDescInt                = True
      FieldTyDescLong                == FieldTyDescLong               = True
      (FieldTyDescReference refTy1)  == (FieldTyDescReference refTy2) = refTy1 == refTy2
      _                              == _                             = False

  Eq TypeDescriptor where
    (FieldDescriptor fieldTyDesc1) == (FieldDescriptor fieldTyDesc2) = fieldTyDesc1 == fieldTyDesc2
    VoidDescriptor == VoidDescriptor = True
    (ThrowableDescriptor tyDesc1) == (ThrowableDescriptor tyDesc2) = tyDesc1 == tyDesc2
    _ == _ = False

  Show ReferenceTypeDescriptor where
    show (ClassDesc className) = "ClassDesc " ++ show className
    show (InterfaceDesc className) = "InterfaceDesc " ++ show className
    show (ArrayDesc tyDesc) = "ArrayDesc " ++ show tyDesc
    show (IdrisExportDesc className) = "IdrisExportDesc " ++ show className

  Show FieldTypeDescriptor where
    show FieldTyDescByte = "FieldTyDescByte"
    show FieldTyDescChar = "FieldTyDescChar"
    show FieldTyDescShort = "FieldTyDescShort"
    show FieldTyDescBoolean = "FieldTyDescBoolean"
    show FieldTyDescDouble = "FieldTyDescDouble"
    show FieldTyDescFloat = "FieldTyDescFloat"
    show FieldTyDescInt = "FieldTyDescInt"
    show FieldTyDescLong = "FieldTyDescLong"
    show (FieldTyDescReference referenceTypeDescriptor) = "FieldTyDescReference(" ++ show referenceTypeDescriptor ++ ")"

  Show TypeDescriptor where
    show (FieldDescriptor fieldTypeDescriptor) = "FieldDescriptor(" ++ show fieldTypeDescriptor ++ ")"
    show VoidDescriptor = "VoidDescriptor"
    show (ThrowableDescriptor tyDesc) = "ThrowableDescriptor(" ++ show tyDesc ++ ")"