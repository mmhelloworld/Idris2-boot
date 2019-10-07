foo : String
foo = "ällo"

ällo : Int
ällo = 42

main : JVM_IO ()
main = do printLn ällo
          putStrLn "ällo"
