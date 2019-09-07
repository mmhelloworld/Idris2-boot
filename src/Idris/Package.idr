module Idris.Package

import Core.Context
import Core.Core
import Core.Directory
import Core.Options
import Core.Unify

import Data.These
import Data.StringMap
import Data.StringTrie

import Idris.CommandLine
import Idris.ModTree
import Idris.ProcessIdr
import Idris.REPLOpts
import Idris.SetOptions
import Idris.Syntax
import Parser.Lexer
import Parser.Support
import Utils.Binary

-- import System
import Text.Parser

import IdrisJvm.IO
import IdrisJvm.System
import IdrisJvm.File

%hide Prelude.File.GenericFileError

%default covering

record PkgDesc where
  constructor MkPkgDesc
  name : String
  version : String
  authors : String
  maintainers : Maybe String
  license : Maybe String
  brief   : Maybe String
  readme  : Maybe String
  homepage : Maybe String
  sourceloc : Maybe String
  bugtracker : Maybe String
  depends : List String -- packages to add to search path
  modules : List (List String, String) -- modules to install (namespace, filename)
  mainmod : Maybe (List String, String) -- main file (i.e. file to load at REPL)
  executable : Maybe String -- name of executable
  options : Maybe (FC, String)
  prebuild : Maybe (FC, String) -- Script to run before building
  postbuild : Maybe (FC, String) -- Script to run after building
  preinstall : Maybe (FC, String) -- Script to run after building, before installing
  postinstall : Maybe (FC, String) -- Script to run after installing

Show PkgDesc where
  show pkg = "Package: " ++ name pkg ++ "\n" ++
             "Version: " ++ version pkg ++ "\n" ++
             "Authors: " ++ authors pkg ++ "\n" ++
             maybe "" (\m => "Maintainers: " ++ m ++ "\n") (maintainers pkg) ++
             maybe "" (\m => "License: "     ++ m ++ "\n") (license pkg)     ++
             maybe "" (\m => "Brief: "       ++ m ++ "\n") (brief pkg)       ++
             maybe "" (\m => "ReadMe: "      ++ m ++ "\n") (readme pkg)      ++
             maybe "" (\m => "HomePage: "    ++ m ++ "\n") (homepage pkg)    ++
             maybe "" (\m => "SourceLoc: "   ++ m ++ "\n") (sourceloc pkg)   ++
             maybe "" (\m => "BugTracker: "  ++ m ++ "\n") (bugtracker pkg)  ++
             "Depends: " ++ show (depends pkg) ++ "\n" ++
             "Modules: " ++ show (map snd (modules pkg)) ++ "\n" ++
             maybe "" (\m => "Main: " ++ snd m ++ "\n") (mainmod pkg) ++
             maybe "" (\m => "Exec: " ++ m ++ "\n") (executable pkg) ++
             maybe "" (\m => "Opts: " ++ snd m ++ "\n") (options pkg) ++
             maybe "" (\m => "Prebuild: " ++ snd m ++ "\n") (prebuild pkg) ++
             maybe "" (\m => "Postbuild: " ++ snd m ++ "\n") (postbuild pkg) ++
             maybe "" (\m => "Preinstall: " ++ snd m ++ "\n") (preinstall pkg) ++
             maybe "" (\m => "Postinstall: " ++ snd m ++ "\n") (postinstall pkg)

initPkgDesc : String -> PkgDesc
initPkgDesc pname
    = MkPkgDesc pname "0" "Anonymous" Nothing Nothing
                Nothing Nothing Nothing Nothing Nothing
                [] []
                Nothing Nothing Nothing Nothing Nothing Nothing Nothing

data DescField : Type where
  PVersion     : FC -> String -> DescField
  PAuthors     : FC -> String -> DescField
  PMaintainers : FC -> String -> DescField
  PLicense     : FC -> String -> DescField
  PBrief       : FC -> String -> DescField
  PReadMe      : FC -> String -> DescField
  PHomePage    : FC -> String -> DescField
  PSourceLoc   : FC -> String -> DescField
  PBugTracker  : FC -> String -> DescField
  PDepends     : List String -> DescField
  PModules     : List (FC, List String) -> DescField
  PMainMod     : FC -> List String -> DescField
  PExec        : String -> DescField
  POpts        : FC -> String -> DescField
  PPrebuild    : FC -> String -> DescField
  PPostbuild   : FC -> String -> DescField
  PPreinstall  : FC -> String -> DescField
  PPostinstall : FC -> String -> DescField

field : String -> Rule DescField
field fname
      = strField PVersion "version"
    <|> strField PAuthors "authors"
    <|> strField PMaintainers "maintainers"
    <|> strField PLicense "license"
    <|> strField PBrief "brief"
    <|> strField PReadMe "readme"
    <|> strField PHomePage "homepage"
    <|> strField PSourceLoc "sourceloc"
    <|> strField PBugTracker "bugtracker"
    <|> strField POpts "options"
    <|> strField POpts "opts"
    <|> strField PPrebuild "prebuild"
    <|> strField PPostbuild "postbuild"
    <|> strField PPreinstall "preinstall"
    <|> strField PPostinstall "postinstall"
    <|> do exactIdent "depends"; symbol "="
           ds <- sepBy1 (symbol ",") unqualifiedName
           pure (PDepends ds)
    <|> do exactIdent "modules"; symbol "="
           ms <- sepBy1 (symbol ",")
                      (do start <- location
                          ns <- namespace_
                          end <- location
                          pure (MkFC fname start end, ns))
           pure (PModules ms)
    <|> do exactIdent "main"; symbol "="
           start <- location
           m <- namespace_
           end <- location
           pure (PMainMod (MkFC fname start end) m)
    <|> do exactIdent "executable"; symbol "="
           e <- unqualifiedName
           pure (PExec e)
  where
    getStr : (FC -> String -> DescField) -> FC ->
             String -> Constant -> EmptyRule DescField
    getStr p fc fld (Str s) = pure (p fc s)
    getStr p fc fld _ = fail $ fld ++ " field must be a string"

    strField : (FC -> String -> DescField) -> String -> Rule DescField
    strField p f
        = do start <- location
             exactIdent f
             symbol "="
             c <- constant
             end <- location
             getStr p (MkFC fname start end) f c

parsePkgDesc : String -> Rule (String, List DescField)
parsePkgDesc fname
    = do exactIdent "package"
         name <- unqualifiedName
         fields <- many (field fname)
         pure (name, fields)

addField : {auto c : Ref Ctxt Defs} ->
           DescField -> PkgDesc -> Core PkgDesc
addField (PVersion fc n) pkg = pure (record { version = n } pkg)
addField (PAuthors fc a) pkg = pure (record { authors = a } pkg)
addField (PMaintainers fc a) pkg = pure (record { maintainers = Just a } pkg)
addField (PLicense fc a) pkg = pure (record { license = Just a } pkg)
addField (PBrief fc a) pkg = pure (record { brief = Just a } pkg)
addField (PReadMe fc a) pkg = pure (record { readme = Just a } pkg)
addField (PHomePage fc a) pkg = pure (record { homepage = Just a } pkg)
addField (PSourceLoc fc a) pkg = pure (record { sourceloc = Just a } pkg)
addField (PBugTracker fc a) pkg = pure (record { bugtracker = Just a } pkg)

addField (PDepends ds) pkg = pure (record { depends = ds } pkg)
addField (PModules ms) pkg
    = pure (record { modules = !(traverse toSource ms) } pkg)
  where
    toSource : (FC, List String) -> Core (List String, String)
    toSource (loc, ns) = pure (ns, !(nsToSource loc ns))
addField (PMainMod loc n) pkg
    = pure (record { mainmod = Just (n, !(nsToSource loc n)) } pkg)
addField (PExec e) pkg = pure (record { executable = Just e } pkg)
addField (POpts fc e) pkg = pure (record { options = Just (fc, e) } pkg)
addField (PPrebuild fc e) pkg = pure (record { prebuild = Just (fc, e) } pkg)
addField (PPostbuild fc e) pkg = pure (record { postbuild = Just (fc, e) } pkg)
addField (PPreinstall fc e) pkg = pure (record { preinstall = Just (fc, e) } pkg)
addField (PPostinstall fc e) pkg = pure (record { postinstall = Just (fc, e) } pkg)

addFields : {auto c : Ref Ctxt Defs} ->
            List DescField -> PkgDesc -> Core PkgDesc
addFields [] desc = pure desc
addFields (x :: xs) desc = addFields xs !(addField x desc)

runScript : Maybe (FC, String) -> Core ()
runScript Nothing = pure ()
runScript (Just (fc, s))
    = do res <- coreLift $ system s
         when (res /= 0) $
            throw (GenericMsg fc "Script failed")

addDeps : {auto c : Ref Ctxt Defs} ->
          PkgDesc -> Core ()
addDeps pkg
    = do defs <- get Ctxt
         traverse addPkgDir (depends pkg)
         pure ()

processOptions : {auto c : Ref Ctxt Defs} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 Maybe (FC, String) -> Core ()
processOptions Nothing = pure ()
processOptions (Just (fc, opts))
    = do let Right clopts = getOpts (words opts)
                | Left err => throw (GenericMsg fc err)
         preOptions clopts

build : {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        {auto o : Ref ROpts REPLOpts} ->
        PkgDesc -> Core (List Error)
build pkg
    = do defs <- get Ctxt
         addDeps pkg
         processOptions (options pkg)
         runScript (prebuild pkg)
         let toBuild = maybe (map snd (modules pkg))
                             (\m => snd m :: map snd (modules pkg))
                             (mainmod pkg)
         [] <- buildAll toBuild
              | errs => pure errs
         runScript (postbuild pkg)
         pure []

copyFile : String -> String -> JVM_IO (Either FileError ())
copyFile src dest
    = do Right buf <- readFromFile src
             | Left err => pure (Left err)
         writeToFile dest buf

installFrom : {auto c : Ref Ctxt Defs} ->
              String -> String -> String -> List String -> Core ()
installFrom _ _ _ [] = pure ()
installFrom pname builddir destdir ns@(m :: dns)
    = do let ttcfile = showSep "/" (reverse ns)
         let ttcPath = builddir ++ dirSep ++ ttcfile ++ ".ttc"
         let destPath = destdir ++ dirSep ++ showSep "/" (reverse dns)
         let destFile = destdir ++ dirSep ++ ttcfile ++ ".ttc"
         Right _ <- coreLift $ mkdirs (reverse dns)
             | Left err => throw (FileErr pname err)
         coreLift $ putStrLn $ "Installing " ++ ttcPath ++ " to " ++ destPath
         Right _ <- coreLift $ copyFile ttcPath destFile
             | Left err => throw (FileErr pname err)
         pure ()

-- Install all the built modules in prefix/package/
-- We've already built and checked for success, so if any don't exist that's
-- an internal error.
install : {auto c : Ref Ctxt Defs} ->
          {auto o : Ref ROpts REPLOpts} ->
          PkgDesc -> Core ()
install pkg
    = do defs <- get Ctxt
         let build = build_dir (dirs (options defs))
         runScript (preinstall pkg)
         let toInstall = maybe (map fst (modules pkg))
                               (\m => fst m :: map fst (modules pkg))
                               (mainmod pkg)
         srcdir <- coreLift currentDir
         -- Make the package installation directory
         let installPrefix = dir_prefix (dirs (options defs)) ++ dirSep ++ "idris2"
         True <- coreLift $ changeDir installPrefix
             | False => throw (FileErr (name pkg) FileReadError)
         Right _ <- coreLift $ mkdirs [name pkg]
             | Left err => throw (FileErr (name pkg) err)
         True <- coreLift $ changeDir (name pkg)
             | False => throw (FileErr (name pkg) FileReadError)

         -- We're in that directory now, so copy the files from
         -- srcdir/build into it
         traverse (installFrom (name pkg)
                               (srcdir ++ dirSep ++ build)
                               (installPrefix ++ dirSep ++ name pkg)) toInstall
         coreLift $ changeDir srcdir
         runScript (postinstall pkg)

-- Data.These.bitraverse hand specialised for Core
bitraverseC : (a -> Core c) -> (b -> Core d) -> These a b -> Core (These c d)
bitraverseC f g (This a)   = [| This (f a) |]
bitraverseC f g (That b)   = [| That (g b) |]
bitraverseC f g (Both a b) = [| Both (f a) (g b) |]

-- Prelude.Monad.foldlM hand specialised for Core
foldlC : Foldable t => (a -> b -> Core a) -> a -> t b -> Core a
foldlC fm a0 = foldl (\ma,b => ma >>= flip fm b) (pure a0)

-- Data.StringTrie.foldWithKeysM hand specialised for Core
foldWithKeysC : Monoid b => (List String -> Core b) -> (List String -> a -> Core b) -> StringTrie a -> Core b
foldWithKeysC {a} {b} fk fv = go []
  where
  go : List String -> StringTrie a -> Core b
  go as (MkStringTrie nd) =
    map bifold $ bitraverseC
                   (fv as)
                   (\sm => foldlC
                             (\x, (k, vs) =>
                               do let as' = as ++ [k]
                                  y <- assert_total $ go as' vs
                                  z <- fk as'
                                  pure $ x <+> y <+> z)
                             neutral
                             (toList sm))
                   nd

Semigroup () where
  (<+>) _ _ = ()

Monoid () where
  neutral = ()

clean : {auto c : Ref Ctxt Defs} ->
        {auto o : Ref ROpts REPLOpts} ->
        PkgDesc -> Core ()
clean pkg
    = do defs <- get Ctxt
         let build = build_dir (dirs (options defs))
         let toClean = mapMaybe (\ks => [| MkPair (tail' ks) (head' ks) |]) $
                       maybe (map fst (modules pkg))
                             (\m => fst m :: map fst (modules pkg))
                             (mainmod pkg)
         srcdir <- coreLift currentDir
         let builddir = srcdir ++ dirSep ++ build
         -- the usual pair syntax breaks with `No such variable a` here for some reason
         let pkgTrie = the (StringTrie (List String)) $
                       foldl (\trie, ksv =>
                                let ks = fst ksv
                                    v = snd ksv
                                  in
                                insertWith ks (maybe [v] (v::)) trie) empty toClean
         foldWithKeysC (deleteFolder builddir)
                       (\ks => map concat . traverse (deleteBin builddir ks))
                       pkgTrie
         deleteFolder builddir []
  where
  delete : String -> Core ()
  delete path = do True <- coreLift $ fRemove path
                     | False => do coreLift $ putStrLn $ path ++ ": " ++ show (GenericFileError (-1))
                   coreLift $ putStrLn $ "Removed: " ++ path
  deleteFolder : String -> List String -> Core ()
  deleteFolder builddir ns = delete $ builddir ++ dirSep ++ showSep "/" (reverse ns)
  deleteBin : String -> List String -> String -> Core ()
  deleteBin builddir ns mod
      = do let ttFile = builddir ++ dirSep ++ showSep "/" (reverse ns) ++ dirSep ++ mod
           delete $ ttFile ++ ".ttc"
           delete $ ttFile ++ ".ttm"

-- Just load the 'Main' module, if it exists, which will involve building
-- it if necessary
runRepl : {auto c : Ref Ctxt Defs} ->
          {auto o : Ref ROpts REPLOpts} ->
          PkgDesc -> Core ()
runRepl pkg
    = do addDeps pkg
         processOptions (options pkg)
         throw (InternalError "Not implemented")

processPackage : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 PkgCommand -> String -> Core ()
processPackage cmd file
    = do Right (pname, fs) <- coreLift $ parseFile file
                                  (do desc <- parsePkgDesc file
                                      eoi
                                      pure desc)
             | Left err => throw (ParseFail (getParseErrorLoc file err) err)
         pkg <- addFields fs (initPkgDesc pname)
         case cmd of
              Build => do [] <- build pkg
                             | errs => coreLift (exit 1)
                          pure ()
              Install => do [] <- build pkg
                               | errs => coreLift (exit 1)
                            install pkg
              Clean => clean pkg
              REPL => runRepl pkg

rejectPackageOpts : List CLOpt -> Core Bool
rejectPackageOpts (Package cmd f :: _)
    = do coreLift $ putStrLn ("Package commands (--build, --install, --clean, --repl) must be the only option given")
         pure True -- Done, quit here
rejectPackageOpts (_ :: xs) = rejectPackageOpts xs
rejectPackageOpts [] = pure False

-- If there's a package option, it must be the only option, so reject if
-- it's not
export
processPackageOpts : {auto c : Ref Ctxt Defs} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     List CLOpt -> Core Bool
processPackageOpts [Package cmd f]
    = do processPackage cmd f
         pure True
processPackageOpts opts = rejectPackageOpts opts
