module Compiler.Jvm.Jvar

import Core.Name
import Core.TT
import Core.FC

%access public export

data Jvar = MkJvar String Nat

jvarIndex : Jvar -> Nat
jvarIndex (MkJvar _ index) = index

jvarName : Jvar -> String
jvarName (MkJvar name _) = name

data Jvars : List Name -> Type where
     Nil  : Jvars []
     (::) : Jvar -> Jvars ns -> Jvars (n :: ns)

extendJvars : Int -> (xs : List Name) -> Jvars ns -> Jvars (xs ++ ns)
extendJvars nextVar xs vs = extJvars' nextVar xs vs
  where
    extJvars' : Int -> (xs : List Name) -> Jvars ns -> Jvars (xs ++ ns)
    extJvars' i [] vs = vs
    extJvars' i (x :: xs) vs =
        let name = jvmSimpleName $ MN (jvmSimpleName x) i
        in MkJvar name (cast i) :: extJvars' (i + 1) xs vs

initJvars : (xs : List Name) -> Jvars xs
initJvars xs = rewrite sym (appendNilRightNeutral xs) in extendJvars 0 xs []

lookupJvar : {idx : Nat} -> .(IsVar n idx xs) -> Jvars xs -> Jvar
lookupJvar First (n :: ns) = n
lookupJvar (Later p) (n :: ns) = lookupJvar p ns

toList : Jvars xs -> List Jvar
toList xs = reverse $ go [] xs where
    go : List Jvar -> Jvars ys -> List Jvar
    go acc [] = acc
    go acc (x :: xs) = go (x :: acc) xs
