module System.Directory

import public System.File

public export
DirPtr : Type
DirPtr = AnyPtr

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

directoriesClass : String
directoriesClass = "io/github/mmhelloworld/idris2boot/runtime/Directories"

ok : a -> IO (Either FileError a)
ok x = pure (Right x)

%foreign
    support "idris2_currentDirectory"
    jvm directoriesClass "getWorkingDirectory"
prim_currentDir : PrimIO (Ptr String)

%foreign
    support "idris2_changeDir"
    jvm directoriesClass "changeDirectory"
prim_changeDir : String -> PrimIO Int

%foreign
    support "idris2_createDir"
    jvm directoriesClass "createDirectory"
prim_createDir : String -> PrimIO Int

%foreign
    support "idris2_dirOpen"
    jvm directoriesClass "openDirectory"
prim_openDir : String -> PrimIO DirPtr

%foreign
    support "idris2_dirClose"
    jvm directoriesClass "closeDirectory"
prim_closeDir : DirPtr -> PrimIO ()

%foreign
    support "idris2_nextDirEntry"
    jvm directoriesClass "getNextDirectoryEntry"
prim_dirEntry : DirPtr -> PrimIO (Ptr String)

export
data Directory : Type where
     MkDir : DirPtr -> Directory

export
createDir : String -> IO (Either FileError ())
createDir dir
    = do res <- primIO (prim_createDir dir)
         if res == 0
            then ok ()
            else returnError

export
changeDir : String -> IO Bool
changeDir dir
    = do ok <- primIO (prim_changeDir dir)
         pure (ok == 0)

export
currentDir : IO (Maybe String)
currentDir
    = do res <- primIO prim_currentDir
         if prim__nullPtr res /= 0
            then pure Nothing
            else pure (Just (prim__getString res))

export
openDir : String -> IO (Either FileError Directory)
openDir d
    = do res <- primIO (prim_openDir d)
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (MkDir res)

export
closeDir : Directory -> IO ()
closeDir (MkDir d) = primIO (prim_closeDir d)

export
dirEntry : Directory -> IO (Either FileError String)
dirEntry (MkDir d)
    = do res <- primIO (prim_dirEntry d)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)
