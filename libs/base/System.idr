module System

import Data.So

%cg chicken (use posix)

export
sleep : Int -> JVM_IO ()
sleep sec = schemeCall () "blodwen-sleep" [sec]

export
usleep : (x : Int) -> So (x >= 0) => JVM_IO ()
usleep usec = schemeCall () "blodwen-usleep" [usec]

export
getArgs : JVM_IO (List String)
getArgs = schemeCall (List String) "blodwen-args" []

export
time : JVM_IO Integer
time = schemeCall Integer "blodwen-time" []
