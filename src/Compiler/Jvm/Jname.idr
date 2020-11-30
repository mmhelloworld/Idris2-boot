module Compiler.Jvm.Jname

import Core.Name

%access public export

data Jname = Jqualified String String
           | Jsimple String

className : Jname -> String
className (Jqualified cname _) = cname
className (Jsimple _) = "main/Main"

methodName : Jname -> String
methodName (Jqualified _ mname) = mname
methodName (Jsimple mname) = mname

cleanupIdentifier : String -> String
cleanupIdentifier s = concatMap transformSpecialChar (unpack s)
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
    transformSpecialChar ',' = "$cma"
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
jvmName (NS ns n) = Jqualified (showSep "/" (cleanupIdentifier <$> reverse ns)) $ getSimpleName (jvmName n)
jvmName (UN n) = Jsimple $ cleanupIdentifier n
jvmName (MN n i) = Jsimple $ cleanupIdentifier n ++ "$" ++ show i
jvmName (PV n d) = Jsimple $ "$patvar" ++ getSimpleName (jvmName n)
jvmName (DN str n) = Jsimple $ cleanupIdentifier str ++ getSimpleName (jvmName n)
jvmName (RF n) = Jsimple $ "$recfield" ++ cleanupIdentifier n
jvmName (Nested (i, x) n) = Jsimple $ "$nested" ++ show i ++ "$" ++ show x ++ "$" ++ getSimpleName (jvmName n)
jvmName (CaseBlock x y) = Jsimple $ "$case" ++ show x ++ "$" ++ show y
jvmName (WithBlock x y) = Jsimple $ "$with" ++ show x ++ "$" ++ show y
jvmName (Resolved i) = Jsimple $ "$resolved" ++ show i

jvmSimpleName : Name -> String
jvmSimpleName = getSimpleName . jvmName

jvmIdrisMainMethodName : String
jvmIdrisMainMethodName = "jvm$idrisMain"

idrisMainFunctionName : Name
idrisMainFunctionName = NS ["Main"] (UN jvmIdrisMainMethodName)