module Compiler.Jvm.Jname

%access public export

data Jname = Jqualified String String
           | Jsimple String

className : Jname -> String
className (Jqualified cname _) = cname
className (Jsimple _) = "main/Main"

methodName : Jname -> String
methodName (Jqualified _ mname) = mname
methodName (Jsimple mname) = mname

getJmethodName : String -> String
getJmethodName s = concatMap transformSpecialChar (unpack s)
  where
    transformSpecialChar : Char -> String
    transformSpecialChar ' ' = "$spc"
    transformSpecialChar '.' = "$dot"
    transformSpecialChar ';' = "$scol"
    transformSpecialChar '[' = "$lsq"
    transformSpecialChar '/' = "$div"
    transformSpecialChar '<' = "$lt"
    transformSpecialChar '>' = "$gt"
    transformSpecialChar ':' = "$col"
    transformSpecialChar c = cast c

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

