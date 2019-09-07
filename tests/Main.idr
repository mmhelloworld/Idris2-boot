module Main

-- import System
import IdrisJvm.IO
import IdrisJvm.File
import IdrisJvm.System

%default covering

ttimpTests : List String
ttimpTests
    = ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006",
       "coverage001", "coverage002",
       "dot001",
       "eta001", "eta002",
       "lazy001",
       "nest001", "nest002",
       "perf001", "perf002", "perf003",
       "record001", "record002",
       "rewrite001",
       "qtt001", "qtt002", "qtt003",
       "search001", "search002", "search003", "search004", "search005",
       "total001", "total002", "total003",
       "with001"]

idrisTests : List String
idrisTests
    = ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006", "basic007", "basic008", "basic009", "basic010",
       "basic011", "basic012", "basic013", "basic014", "basic015",
       "basic016", "basic017", "basic018", "basic019", "basic020",
       "basic021", "basic022", "basic023", "basic024", "basic025",
       "basic026", "basic027", "basic028",
       "coverage001", "coverage002", "coverage003", "coverage004",
       "error001", "error002", "error003", "error004", "error005",
       "error006", "error007", "error008", "error009", "error010",
       "import001", "import002", "import003",
       "interactive001", "interactive002", "interactive003", "interactive004",
       "interactive005", "interactive006", "interactive007", "interactive008",
       "interactive009", "interactive010", "interactive011", "interactive012",
       "interface001", "interface002", "interface003", "interface004",
       "interface005", "interface006", "interface007", "interface008",
       "interface009", "interface010", "interface011", "interface012",
       "interface013",
       "lazy001",
       "linear001", "linear002", "linear003", "linear004", "linear005",
       "linear006", "linear007",
       "perf001", "perf002",
       "perror001", "perror002", "perror003", "perror004", "perror005",
       "perror006",
       "pkg001",
       "record001", "record002",
       "reg001",
       "total001", "total002", "total003", "total004", "total005",
       "total006",
       "with001"]

typeddTests : List String
typeddTests
   = ["chapter01", "chapter02", "chapter03", "chapter04", "chapter05",
      "chapter06", "chapter07", "chapter08", "chapter09", "chapter10",
      "chapter11", "chapter12"]

chezTests : List String
chezTests
   = ["chez001", "chez002", "chez003", "chez004",
      "chez005", "chez006", "chez007"]

chdir : String -> JVM_IO Bool
chdir dir 
    = changeDir dir

fail : String -> JVM_IO ()
fail err
    = do putStrLn err
         exitWith (ExitFailure 1)

runTest : String -> String -> JVM_IO Bool
runTest prog testPath
    = do chdir testPath
         putStr $ testPath ++ ": "
         system $ "sh -c \"./run " ++ prog ++ " | tr -d '\\r' > output\""
         Right out <- readFile "output"
               | Left err => do print err
                                chdir "../.."
                                pure False
         Right exp <- readFile "expected"
               | Left err => do print err
                                chdir "../.."
                                pure False

         if (out == exp)
            then putStrLn "success"
            else do
              putStrLn "FAILURE"
              putStrLn "Expected:"
              printLn exp
              putStrLn "Given:"
              printLn out
         chdir "../.."
         pure (out == exp)

exists : String -> JVM_IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

firstExists : List String -> JVM_IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

findChez : JVM_IO (Maybe String)
findChez
    = do env <- getEnv "CHEZ"
         case env of
            Just n => pure $ Just n
            Nothing => firstExists [p ++ x | p <- ["/usr/bin/", "/usr/local/bin/"],
                                    x <- ["scheme", "chez", "chezscheme9.5"]]

runChezTests : String -> List String -> JVM_IO (List Bool)
runChezTests prog tests
    = do chexec <- findChez
         maybe (do putStrLn "Chez Scheme not found"
                   pure [])
               (\c => do putStrLn $ "Found Chez Scheme at " ++ c
                         traverse (runTest prog) tests)
               chexec

main : JVM_IO ()
main
    = do args <- getArgs
         let (_ :: idris2 :: _) = args
              | _ => do putStrLn "Usage: runtests <idris2 path> [--only <name>]"
         let filterTests = case drop 2 args of
              ("--only" :: onlyName :: _) => filter (\testName => isInfixOf onlyName testName)
              _ => id
         let filteredNonCGTests =
              filterTests $ concat [testPaths "ttimp" ttimpTests,
                                    testPaths "idris2" idrisTests,
                                    testPaths "typedd-book" typeddTests]
         let filteredChezTests = filterTests (testPaths "chez" chezTests)
         nonCGTestRes <- traverse (runTest idris2) filteredNonCGTests
         chezTestRes <- if length filteredChezTests > 0
              then runChezTests idris2 filteredChezTests
              else pure []
         let res = nonCGTestRes ++ chezTestRes
         putStrLn (show (length (filter id res)) ++ "/" ++ show (length res)
                       ++ " tests successful")
         if (any not res)
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess
    where
         testPaths : String -> List String -> List String
         testPaths dir tests = map (\test => dir ++ "/" ++ test) tests
