module Main

import System.REPL

main : JVM_IO ()
main = repl "> " reverse
