module Compiler.Jvm.Jvar

data Jvar = MkJvar String Nat

implementation Eq Jvar where
    (MkJvar name1 index1) == (MkJvar name2 index2) = name1 == name2 && index1 == index2

implementation Ord Jvar where
  compare (MkJvar _ index1) (MkJvar _ index2) = compare index1 index2

implementation Show Jvar where
    show (MkJvar name index) = "JVar " ++ show name ++ " " ++ show index