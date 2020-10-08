module Compiler.Scheme.Gambit

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Utils.Hex

import Data.NameMap
import Data.Vect
import System.Info

import IdrisJvm.IO
import IdrisJvm.System
import IdrisJvm.File

%default covering

-- TODO Look for gsi-script, then gsi
findGSI : JVM_IO String
findGSI =
  do env <- getEnv "GAMBIT_GSI"
     pure $ fromMaybe "/usr/bin/env -S gsi" env

-- TODO Look for gsc-script, then gsc
findGSC : JVM_IO String
findGSC =
  do env <- getEnv "GAMBIT_GSC"
     pure $ fromMaybe "/usr/bin/env -S gsc" env

schHeader : String
schHeader = "(declare (block)
         (inlining-limit 450)
         (standard-bindings)
         (extended-bindings)
         (not safe)
         (optimize-dead-definitions))\n"

showGambitChar : Char -> String -> String
showGambitChar '\\' = ("\\\\" ++)
showGambitChar c
   = if c < chr 32 -- XXX
        then (("\\x" ++ asHex (cast c) ++ ";") ++)
        else strCons c

showGambitString : List Char -> String -> String
showGambitString [] = id
showGambitString ('"'::cs) = ("\\\"" ++) . showGambitString cs
showGambitString (c::cs) = (showGambitChar c) . showGambitString cs

gambitString : String -> String
gambitString cs = strCons '"' (showGambitString (unpack cs) "\"")

mutual
  -- Primitive types have been converted to names for the purpose of matching
  -- on types
  tySpec : NamedCExp -> Core String
  tySpec (NmCon fc (UN "Int") _ []) = pure "int"
  tySpec (NmCon fc (UN "String") _ []) = pure "UTF-8-string"
  tySpec (NmCon fc (UN "Double") _ []) = pure "double"
  tySpec (NmCon fc (UN "Char") _ []) = pure "char"
  tySpec (NmCon fc (NS _ n) _ [_])
     = cond [(n == UN "Ptr", pure "(pointer void)")]
          (throw (GenericMsg fc ("Can't pass argument of type " ++ show n ++ " to foreign function")))
  tySpec (NmCon fc (NS _ n) _ [])
     = cond [(n == UN "Unit", pure "void"),
             (n == UN "AnyPtr", pure "(pointer void)")]
          (throw (GenericMsg fc ("Can't pass argument of type " ++ show n ++ " to foreign function")))
  tySpec ty = throw (GenericMsg (getFC ty) ("Can't pass argument of type " ++ show ty ++ " to foreign function"))

  handleRet : String -> String -> String
  handleRet "void" op = op ++ " " ++ mkWorld (schConstructor gambitString (UN "") (Just 0) [])
  handleRet _ op = mkWorld op

  getFArgs : NamedCExp -> Core (List (NamedCExp, NamedCExp))
  getFArgs (NmCon fc _ (Just 0) _) = pure []
  getFArgs (NmCon fc _ (Just 1) [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
  getFArgs arg = throw (GenericMsg (getFC arg) ("Badly formed c call argument list " ++ show arg))

  gambitPrim : Int -> ExtPrim -> List NamedCExp -> Core String
  gambitPrim i CCall [ret, NmPrimVal fc (Str fn), fargs, world]
      = do args <- getFArgs fargs
           argTypes <- traverse tySpec (map fst args)
           retType <- tySpec ret
           argsc <- traverse (schExp gambitPrim gambitString 0) (map snd args)
           pure $ handleRet retType ("((c-lambda (" ++ showSep " " argTypes ++ ") "
                    ++ retType ++ " " ++ show fn ++ ") "
                    ++ showSep " " argsc ++ ")")
  gambitPrim i CCall [ret, fn, args, world]
      = pure "(error \"bad ffi call\")"
  gambitPrim i GetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _]
      = do structsc <- schExp gambitPrim gambitString 0 struct
           pure $ "(" ++ s ++ "-" ++ fld ++ " " ++ structsc ++ ")"
  gambitPrim i GetField [_,_,_,_,_,_]
      = pure "(error \"bad getField\")"
  gambitPrim i SetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _, val, world]
      = do structsc <- schExp gambitPrim gambitString 0 struct
           valsc <- schExp gambitPrim gambitString 0 val
           pure $ mkWorld $
                "(" ++ s ++ "-" ++ fld ++ "-set! " ++ structsc ++ " " ++ valsc ++ ")"
  gambitPrim i SetField [_,_,_,_,_,_,_,_]
      = pure "(error \"bad setField\")"
  gambitPrim i SysCodegen []
      = pure $ "\"gambit\""
  gambitPrim i prim args
      = schExtCommon gambitPrim gambitString i prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

-- Label for noting which struct types are declared
data Structs : Type where

cftySpec : FC -> CFType -> Core String
cftySpec fc CFUnit = pure "void"
cftySpec fc CFInt = pure "int"
cftySpec fc CFString = pure "UTF-8-string"
cftySpec fc CFDouble = pure "double"
cftySpec fc CFChar = pure "char"
cftySpec fc CFPtr = pure "(pointer void)"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ n ++ "*/nonnull"
cftySpec fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core String
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cftySpec fc retty
             argspecs <- traverse (cftySpec fc) (reverse args)
             pure $ "(function (" ++ showSep " " argspecs ++ ") " ++ rtyspec ++ ")"
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))

cCall : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> (cfn : String) -> (clib : String) ->
        List (Name, CFType) -> CFType -> Core String
cCall fc cfn clib args ret
    = do -- loaded <- get Loaded
         -- lib <- if clib `elem` loaded
         --           then pure ""
         --           else do (fname, fullname) <- locate clib
         --                   copyLib (fname, fullname)
         --                   put Loaded (clib :: loaded)
         --                   pure ""
         argTypes <- traverse (\a => cftySpec fc (snd a)) args
         retType <- cftySpec fc ret
         let call = "((c-lambda (" ++ showSep " " argTypes ++ ") "
                      ++ retType ++ " " ++ show cfn ++ ") "
                      ++ showSep " " !(traverse buildArg args) ++ ")"

         pure $ case ret of -- XXX
                     CFIORes _ => handleRet retType call
                     _ => call
  where
    mkNs : Int -> List CFType -> List (Maybe String)
    mkNs i [] = []
    mkNs i (CFWorld :: xs) = Nothing :: mkNs i xs
    mkNs i (x :: xs) = Just ("cb" ++ show i) :: mkNs (i + 1) xs

    applyLams : String -> List (Maybe String) -> String
    applyLams n [] = n
    applyLams n (Nothing :: as) = applyLams ("(" ++ n ++ " #f)") as
    applyLams n (Just a :: as) = applyLams ("(" ++ n ++ " " ++ a ++ ")") as

    mkFun : List CFType -> CFType -> String -> String
    mkFun args ret n
        = let argns = mkNs 0 args in
              "(lambda (" ++ showSep " " (mapMaybe id argns) ++ ") "
              ++ (applyLams n argns ++ ")")

    notWorld : CFType -> Bool
    notWorld CFWorld = False
    notWorld _ = True

    callback : String -> List CFType -> CFType -> Core String
    callback n args (CFFun s t) = callback n (s :: args) t
    callback n args_rev retty
        = do let args = reverse args_rev
             argTypes <- traverse (cftySpec fc) (filter notWorld args)
             retType <- cftySpec fc retty
             pure $ mkFun args retty n -- FIXME Needs a top-level c-define

    buildArg : (Name, CFType) -> Core String
    buildArg (n, CFFun s t) = callback (schName n) [s] t
    buildArg (n, _) = pure $ schName n

schemeCall : FC -> (sfn : String) ->
             List Name -> CFType -> Core String
schemeCall fc sfn argns ret
    = let call = "(" ++ sfn ++ " " ++ showSep " " (map schName argns) ++ ")" in
          case ret of
               CFIORes _ => pure $ mkWorld call
               _ => pure call

-- Use a calling convention to compile a foreign def.
-- Returns the name of the static library to link and the body
-- of the function call.
useCC : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> List String -> List (Name, CFType) -> CFType -> Core (Maybe String, String)
useCC fc [] args ret
    = throw (GenericMsg fc "No recognised foreign calling convention")
useCC fc (cc :: ccs) args ret
    = case parseCC cc of
           Nothing => useCC fc ccs args ret
           Just ("scheme", [sfn]) => pure (Nothing, !(schemeCall fc sfn (map fst args) ret))
           Just ("C", [cfn, clib]) => pure (Just clib, !(cCall fc cfn clib args ret))
           Just ("C", [cfn, clib, chdr]) => pure (Just clib, !(cCall fc cfn clib args ret))
           _ => useCC fc ccs args ret

-- For every foreign arg type, return a name, and whether to pass it to the
-- foreign call (we don't pass '%World')
mkArgs : Int -> List CFType -> List (Name, Bool)
mkArgs i [] = []
mkArgs i (CFWorld :: cs) = (MN "farg" i, False) :: mkArgs i cs
mkArgs i (c :: cs) = (MN "farg" i, True) :: mkArgs (i + 1) cs

mkStruct : {auto s : Ref Structs (List String)} ->
           CFType -> Core String
mkStruct (CFStruct n flds)
    = do defs <- traverse mkStruct (map snd flds)
         strs <- get Structs
         if n `elem` strs
            then pure (concat defs)
            else do put Structs (n :: strs)
                    pure $ concat defs ++ "(define-c-struct " ++ n ++ " "
                           ++ showSep " " !(traverse showFld flds) ++ ")\n"
  where
    showFld : (String, CFType) -> Core String
    showFld (n, ty) = pure $ "(" ++ n ++ " " ++ !(cftySpec emptyFC ty) ++ ")"
mkStruct (CFIORes t) = mkStruct t
mkStruct (CFFun a b) = do mkStruct a; mkStruct b
mkStruct _ = pure ""

schFgnDef : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref Loaded (List String)} ->
            {auto s : Ref Structs (List String)} ->
            FC -> Name -> NamedDef -> Core (Maybe String, String)
schFgnDef fc n (MkNmForeign cs args ret)
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         argStrs <- traverse mkStruct args
         retStr <- mkStruct ret
         (lib, body) <- useCC fc cs (zip useargns args) ret
         defs <- get Ctxt
         pure (lib,
                concat argStrs ++ retStr ++
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ showSep " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ = pure (Nothing, "")

getFgnCall : {auto c : Ref Ctxt Defs} ->
             {auto l : Ref Loaded (List String)} ->
             {auto s : Ref Structs (List String)} ->
             (Name, FC, NamedDef) -> Core (Maybe String, String)
getFgnCall (n, fc, d) = schFgnDef fc n d

compileToSCM : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core (List String)
compileToSCM c tm outfile
    = do cdata <- getCompileData Cases tm
         let ndefs = namedDefs cdata
         -- let tags = nameTags cdata
         let ctm = forget (mainExpr cdata)

         defs <- get Ctxt
         l <- newRef {t = List String} Loaded []
         s <- newRef {t = List String} Structs []
         fgndefs <- traverse getFgnCall ndefs
         compdefs <- traverse (getScheme gambitPrim gambitString) ndefs
         let code = fastAppend (map snd fgndefs ++ compdefs)
         main <- schExp gambitPrim gambitString 0 ctm
         support <- readDataFile "gambit/support.scm"
         foreign <- readDataFile "gambit/foreign.scm"
         let scm = showSep "\n" [schHeader, support, foreign, code, main]
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         pure $ mapMaybe fst fgndefs

compileExpr : Ref Ctxt Defs -> (execDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c execDir tm outfile
    = do let outn = execDir ++ dirSep ++ outfile ++ ".scm"
         libsname <- compileToSCM c tm outn
         libsfile <- traverse findLibraryFile $ nub $ map (++ ".a") libsname
         gsc <- coreLift findGSC
         let cmd = gsc ++ 
                   " -exe -cc-options \"-Wno-implicit-function-declaration\" -ld-options \"" ++
                   (showSep " " libsfile)  ++ "\" " ++ outn
         ok <- coreLift $ system cmd
         if ok == 0
            then pure (Just (execDir ++ dirSep ++ outfile))
            else pure Nothing

executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c execDir tm
    = do outn <- compileExpr c execDir tm "_tmpgambit"
         case outn of
              -- TODO: on windows, should add exe extension 
              Just outn => map (const ()) $ coreLift $ system outn
              Nothing => pure ()

export
codegenGambit : Codegen
codegenGambit = MkCG compileExpr executeExpr
