libcb : String -> String
libcb f = "C:" ++ f ++", libcb"

%foreign libcb "add"
add : Int -> Int -> Int

%foreign libcb "applyIntFn"
prim_applyIntFn : Int -> Int -> (Int -> Int -> PrimIO Int) -> PrimIO Int

%foreign libcb "applyCharFn"
prim_applyCharFn : Char -> Int -> (Char -> Int -> PrimIO Char) -> PrimIO Char

%foreign libcb "applyIntFnPure"
applyIntFnPure : Int -> Int -> (Int -> Int -> Int) -> Int

applyIntFn : Int -> Int -> (Int -> Int -> JVM_IO Int) -> JVM_IO Int
applyIntFn x y fn
    = primIO $ prim_applyIntFn x y (\a, b => toPrim (fn a b))

applyCharFn : Char -> Int -> (Char -> Int -> JVM_IO Char) -> JVM_IO Char
applyCharFn x y fn
    = primIO $ prim_applyCharFn x y (\a, b => toPrim (fn a b))

cb : Int -> Int -> JVM_IO Int
cb x y
    = do putStrLn $ "In callback with " ++ show (x, y)
         pure (x + y)

main : IO ()
main
    = do printLn (add 4 5)
         res <- applyIntFn (add 4 5) 6 (\x, y => do putStrLn "In callback"
                                                    pure (x * 2 + y))
         printLn res
         res <- applyIntFn 1 2 cb
         printLn res
         printLn (applyIntFnPure 5 4 (\x, y => x + y))
         res <- applyCharFn 'a' 10 (\x, y => pure (cast (cast x + y)))
         printLn res
