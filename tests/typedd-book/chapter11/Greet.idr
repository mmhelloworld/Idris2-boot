-- %default total

data InfIO : Type where
     Do : JVM_IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : JVM_IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

greet : InfIO
greet = do putStr "Enter your name: "
           name <- getLine
           putStrLn ("Hello " ++ name)
           greet
