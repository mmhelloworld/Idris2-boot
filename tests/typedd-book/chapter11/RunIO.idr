-- %default total

data RunIO : Type -> Type where
     Quit : a -> RunIO a
     Do : JVM_IO a -> (a -> Inf (RunIO b)) -> RunIO b

(>>=) : JVM_IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

greet : RunIO ()
greet = do putStr "Enter your name: "
           name <- getLine
           if name == ""
              then do putStrLn "Bye bye!"
                      Quit ()
              else do putStrLn ("Hello " ++ name)
                      greet

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> RunIO a -> JVM_IO (Maybe a)
run fuel (Quit val) = do pure (Just val)
run (More fuel) (Do c f) = do res <- c
                              run fuel (f res)
run Dry p = pure Nothing

partial
forever : Fuel
forever = More forever

partial
main : JVM_IO ()
main = do run forever greet
          pure ()
