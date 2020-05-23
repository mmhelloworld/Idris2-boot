module Compiler.Jvm.Annotation

%access public export

mutual
  data Annotation = MkAnnotation String (List AnnotationProperty)

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
                       | AnnArray (List AnnotationValue)
                       | AnnAnnotation Annotation

  AnnotationProperty : Type
  AnnotationProperty = (String, AnnotationValue)