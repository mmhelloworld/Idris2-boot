module Yaffle.Main

import Parser.Support

import Core.Binary
import Core.Context
import Core.Directory
import Core.Env
import Core.FC
import Core.InitPrimitives
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.TT
import Core.UnifyState

import TTImp.Parser
import TTImp.ProcessDecls
import TTImp.TTImp

import Yaffle.REPL

import IdrisJvm.IO
import IdrisJvm.System

usage : String
usage = "Usage: yaffle <input file> [--timing]"

processArgs : List String -> Core Bool
processArgs [] = pure False
processArgs ["--timing"] = pure True
processArgs _
    = coreLift $ do putStrLn usage
                    exitWith (ExitFailure 1)

HasNames () where
  full _ _ = pure ()
  resolved _ _ = pure ()

export
yaffleMain : String -> List String -> Core ()
yaffleMain fname args
    = do defs <- initDefs
         c <- newRef Ctxt defs
         m <- newRef MD initMetadata
         u <- newRef UST initUState
         d <- getDirs
         t <- processArgs args
         setLogTimings t
         addPrimitives
         case span (/= '.') fname of
              (_, ".ttc") => do coreLift $ putStrLn "Processing as TTC"
                                readFromTTC {extra = ()} emptyFC True fname [] []
                                coreLift $ putStrLn "Read TTC"
              _ => do coreLift $ putStrLn "Processing as TTImp"
                      ok <- processTTImpFile fname
                      when ok $
                         do makeBuildDirectory (pathToNS (working_dir d) (source_dir d) fname)
                            writeToTTC () !(getTTCFileName fname ".ttc")
                            coreLift $ putStrLn "Written TTC"
         ust <- get UST

         repl {c} {u}

{-
main : JVM_IO ()
main
    = do (_ :: fname :: rest) <- getArgs
             | _ => do putStrLn usage
                       exitWith (ExitFailure 1)
         coreRun (yaffleMain fname rest)
               (\err : Error => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
-}
