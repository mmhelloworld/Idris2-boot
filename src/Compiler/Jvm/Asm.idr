module Compiler.Jvm.Asm

import Core.Name
import Core.TT
import Core.FC

import IdrisJvm.IO

%access public export

namespace Assembler

    AssemblerClass : JVM_NativeTy
    AssemblerClass = Class "io/github/mmhelloworld/idris2/jvmassembler/Assembler"

    Assembler : Type
    Assembler = JVM_Native AssemblerClass

data Jname = Jqualified String String
           | Jsimple String

className : Jname -> String
className (Jqualified cname _) = cname
className (Jsimple _) = "main/Main"

methodName : Jname -> String
methodName (Jqualified _ mname) = mname
methodName (Jsimple mname) = mname

getJmethodName : String -> String
getJmethodName s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar ' ' = "$spc"
    okchar '.' = "$dot"
    okchar ';' = "$scol"
    okchar '[' = "$lsq"
    okchar '/' = "$div"
    okchar '<' = "$lt"
    okchar '>' = "$gt"
    okchar ':' = "$col"
    okchar c = cast c

getSimpleName : Jname -> String
getSimpleName (Jsimple n) = n
getSimpleName (Jqualified q n) = q ++ "/" ++ n

implementation Eq Jname where
    name1 == name2 = getSimpleName name1 == getSimpleName name2

implementation Ord Jname where
  compare name1 name2 = compare (getSimpleName name1) (getSimpleName name2)

implementation Show Jname where
    show = getSimpleName

jvmName : Name -> Jname
jvmName (NS ns n) = Jqualified (showSep "/" (reverse ns)) $ getSimpleName (jvmName n)
jvmName (UN n) = Jsimple $ getJmethodName n
jvmName (MN n i) = Jsimple $ getJmethodName n ++ "$" ++ show i
jvmName (PV n d) = Jsimple $ "#p" ++ getSimpleName (jvmName n)
jvmName (DN _ n) = jvmName n
jvmName (Nested i n) = Jsimple $ "#n" ++ show i ++ "_" ++ getSimpleName (jvmName n)
jvmName (CaseBlock x y) = Jsimple $ "#c" ++ show x ++ "_" ++ show y
jvmName (WithBlock x y) = Jsimple $ "#w" ++ show x ++ "_" ++ show y
jvmName (Resolved i) = Jsimple $ "#r" ++ show i

jvmSimpleName : Name -> String
jvmSimpleName = getSimpleName . jvmName

data JVar = MkJVar String Nat

jvarIndex : JVar -> Nat
jvarIndex (MkJVar _ index) = index

jvarName : JVar -> String
jvarName (MkJVar name _) = name

data JVars : List Name -> Type where
     Nil  : JVars []
     (::) : JVar -> JVars ns -> JVars (n :: ns)

extendJVars : Int -> (xs : List Name) -> JVars ns -> JVars (xs ++ ns)
extendJVars nextVar xs vs = extJVars' nextVar xs vs
  where
    extJVars' : Int -> (xs : List Name) -> JVars ns -> JVars (xs ++ ns)
    extJVars' i [] vs = vs
    extJVars' i (x :: xs) vs =
        let name = jvmSimpleName $ MN (jvmSimpleName x) i
        in MkJVar name (cast i) :: extJVars' (i + 1) xs vs

initJVars : (xs : List Name) -> JVars xs
initJVars xs = rewrite sym (appendNilRightNeutral xs) in extendJVars 0 xs []

lookupJVar : {idx : Nat} -> .(IsVar n idx xs) -> JVars xs -> JVar
lookupJVar First (n :: ns) = n
lookupJVar (Later p) (n :: ns) = lookupJVar p ns

toList : JVars xs -> List JVar
toList xs = reverse $ go [] xs where
    go : List JVar -> JVars ys -> List JVar
    go acc [] = acc
    go acc (x :: xs) = go (x :: acc) xs

lineSeparator : String
lineSeparator = unsafePerformIO $ invokeStatic (Class "java/lang/System") "lineSeparator" (JVM_IO String)

startLineNumber : FC -> Int
startLineNumber = fst . startPos

endLineNumber : FC -> Int
endLineNumber = fst . endPos

instruction : List String -> String
instruction = showSep " "

instructions : List (List String) -> String
instructions xxs = showSep lineSeparator (instruction <$> xxs)

createMethod : Jname -> Nat -> String -> String
createMethod name nargs body =
    let cname = className name
        mname = methodName name
    in instructions [
        ["createMethod", cname, mname, show nargs],
        [body],
        ["areturn"]
    ] ++ lineSeparator

lineNumber : Int -> String
lineNumber 0 = ""
lineNumber n = "lineNumber " ++ show n

localVariable : String -> Int -> Int -> String
localVariable _ 0 0 = ""
localVariable n start end = instruction ["localVariable", show start, show end]

aload : FC -> JVar -> String
aload fc (MkJVar name var) =
    let lineStart = startLineNumber fc
        lineEnd = endLineNumber fc

    in instructions [
        [lineNumber lineStart],
        [localVariable name lineStart lineEnd],
        ["aload", show var]
    ]

astore : FC -> JVar -> String -> String
astore fc (MkJVar name var) val =
    instructions [
        [val],
        ["astore", show var]
    ]

loadVar : JVar -> String
loadVar (MkJVar _ var) = "aload " ++ show var

lambda : FC -> JVars vars -> String -> String
lambda fc jvars body =
    let vars = toList jvars
        sortedVars = sortBy (\x, y => compare (jvarIndex x) (jvarIndex y)) vars
        loadedClosures = showSep lineSeparator $ loadVar <$> sortedVars
    in instructions [
        [loadedClosures],
        ["lambda", show (length vars)],
        [body],
        ["endLambda"]
    ]

newBigInteger : String -> String
newBigInteger "0" = instruction ["field", "getStatic", "java/math/BigInteger", "ZERO", "Ljava/math/BigInteger;"]
newBigInteger "1" = instruction ["field", "getStatic", "java/math/BigInteger", "ONE", "Ljava/math/BigInteger;"]
newBigInteger "10" = instruction ["field", "getStatic", "java/math/BigInteger", "TEN", "Ljava/math/BigInteger;"]
newBigInteger i = instructions [
  ["new", "java/math/BigInteger"],
  ["dup"],
  ["ldc", "StringConst " ++ show i],
  ["invokeSpecial", "java/math/BigInteger", "<init>", "(Ljava/lang/String;)V", "false"]
]
