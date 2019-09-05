printTwoThings : JVM_IO ()
printTwoThings = do putStrLn "Hello"
                    putStrLn "World"

printInput : JVM_IO ()
printInput = do x <- getLine
                putStrLn x

printLength : JVM_IO ()
printLength = do putStr "Input string: "
                 input <- getLine
                 let len = length input
                 putStrLn (show len)
