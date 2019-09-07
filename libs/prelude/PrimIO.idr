module PrimIO

import Builtin

public export
data IORes : Type -> Type where
     MkIORes : (result : a) -> (1 x : %World) -> IORes a

export
data JVM_IO : Type -> Type where
     MkJVM_IO : (1 fn : (1 x : %World) -> IORes a) -> JVM_IO a

export
io_pure : a -> JVM_IO a
io_pure x = MkJVM_IO (\w => MkIORes x w)

export
io_bind : (1 act : JVM_IO a) -> (1 k : a -> JVM_IO b) -> JVM_IO b
io_bind (MkJVM_IO fn)
    = \k => MkJVM_IO (\w => let MkIORes x' w' = fn w
                                MkJVM_IO res = k x' in
                                res w')

%extern prim__putStr : String -> (1 x : %World) -> IORes ()
%extern prim__getStr : (1 x : %World) -> IORes String

public export
data Ptr : Type where

public export
data ThreadID : Type where

public export
data FArgList : Type where
     Nil : FArgList
     (::) : {a : Type} -> (1 arg : a) -> (1 args : FArgList) -> FArgList

%extern prim__cCall : (ret : Type) -> String -> (1 args : FArgList) -> 
                      (1 x : %World) -> IORes ret
%extern prim__schemeCall : (ret : Type) -> String -> (1 args : FArgList) -> 
                           (1 x : %World) -> IORes ret

export %inline
primIO : (1 fn : (1 x : %World) -> IORes a) -> JVM_IO a
primIO op = MkJVM_IO op

export %inline
schemeCall : (ret : Type) -> String -> (1 args : FArgList) -> JVM_IO ret
schemeCall ret fn args = primIO (prim__schemeCall ret fn args)
 
export %inline
cCall : (ret : Type) -> String -> FArgList -> JVM_IO ret
cCall ret fn args = primIO (prim__cCall ret fn args)
 
export
putStr : String -> JVM_IO ()
putStr str = primIO (prim__putStr str)

export
putStrLn : String -> JVM_IO ()
putStrLn str = putStr (prim__strAppend str "\n")

export
getLine : JVM_IO String
getLine = primIO prim__getStr

export
fork : (1 prog : JVM_IO ()) -> JVM_IO ThreadID
fork (MkJVM_IO act) = schemeCall ThreadID "blodwen-thread" [act]

unsafeCreateWorld : (1 f : (1 x : %World) -> a) -> a
unsafeCreateWorld f = f %MkWorld

unsafeDestroyWorld : (1 x : %World) -> a -> a
unsafeDestroyWorld %MkWorld x = x

export
unsafePerformIO : JVM_IO a -> a
unsafePerformIO (MkJVM_IO f)
    = unsafeCreateWorld (\w => case f w of
                               MkIORes res w' => unsafeDestroyWorld w' res)
