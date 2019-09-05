module System.Concurrency.Raw

-- Mutexes and condition variables.

%cg chicken (use srfi-18)

export
threadID : JVM_IO ThreadID
threadID = schemeCall ThreadID "blodwen-thisthread" []

export
setThreadData : {a : Type} -> a -> JVM_IO ()
setThreadData val = schemeCall () "blodwen-set-thread-data" [val]

export
getThreadData : (a : Type) -> JVM_IO a
getThreadData a = schemeCall a "blodwen-get-thread-data" []

export
data Mutex : Type where

export
makeMutex : JVM_IO Mutex
makeMutex = schemeCall Mutex "blodwen-mutex" []

export
mutexAcquire : Mutex -> JVM_IO ()
mutexAcquire m = schemeCall () "blodwen-lock" [m]

export
mutexRelease : Mutex -> JVM_IO ()
mutexRelease m = schemeCall () "blodwen-unlock" [m]

export
data Condition : Type where

export
makeCondition : JVM_IO Condition
makeCondition = schemeCall Condition "blodwen-condition" []

export
conditionWait : Condition -> Mutex -> JVM_IO ()
conditionWait c m = schemeCall () "blodwen-condition-wait" [c, m]

export
conditionWaitTimeout : Condition -> Mutex -> Int -> JVM_IO ()
conditionWaitTimeout c m t
    = schemeCall () "blodwen-condition-wait-timeout" [c, m, t]

export
conditionSignal : Condition -> JVM_IO ()
conditionSignal c = schemeCall () "blodwen-condition-signal" [c]

export
conditionBroadcast : Condition -> JVM_IO ()
conditionBroadcast c = schemeCall () "blodwen-condition-broadcast" [c]

