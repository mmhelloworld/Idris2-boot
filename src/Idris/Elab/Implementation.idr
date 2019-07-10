module Idris.Elab.Implementation

import Core.Binary
import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.TT
import Core.Unify

import Idris.Resugar
import Idris.Syntax

import TTImp.BindImplicits
import TTImp.ProcessDecls
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Unelab
import TTImp.TTImp
import TTImp.Utils

import Control.Monad.State
import Data.ANameMap
import Data.NameMap

%default covering

mkImpl : FC -> Name -> List RawImp -> Name
mkImpl fc n ps 
    = DN (show n ++ " implementation at " ++ show fc)
         (UN ("__Impl_" ++ show n ++ "_" ++
          showSep "_" (map show ps)))

bindConstraints : FC -> PiInfo -> 
                  List (Maybe Name, RawImp) -> RawImp -> RawImp
bindConstraints fc p [] ty = ty
bindConstraints fc p ((n, ty) :: rest) sc
    = IPi fc RigW p n ty (bindConstraints fc p rest sc)

addDefaults : FC -> List Name -> List (Name, List ImpClause) ->
              List ImpDecl -> 
              (List ImpDecl, List Name) -- Updated body, list of missing methods
addDefaults fc ms defs body
    = let missing = dropGot ms body in
          extendBody [] missing body
  where
    extendBody : List Name -> List Name -> List ImpDecl -> 
                 (List ImpDecl, List Name)
    extendBody ms [] body = (body, ms)
    extendBody ms (n :: ns) body
        = case lookup n defs of
               Nothing => extendBody (n :: ms) ns body
               Just cs => extendBody ms ns 
                              (IDef fc n (map (substLocClause fc) cs) :: body)

    dropGot : List Name -> List ImpDecl -> List Name
    dropGot ms [] = ms
    dropGot ms (IDef _ n _ :: ds)
        = dropGot (filter (/= n) ms) ds
    dropGot ms (_ :: ds) = dropGot ms ds

export
elabImplementation : {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST UState} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto m : Ref MD Metadata} ->
                     FC -> Visibility -> Pass ->
                     Env Term vars -> NestedNames vars ->
                     (constraints : List (Maybe Name, RawImp)) ->
                     Name ->
                     (ps : List RawImp) ->
                     (implName : Maybe Name) ->
                     Maybe (List ImpDecl) ->
                     Core ()
-- TODO: Refactor all these steps into separate functions
elabImplementation {vars} fc vis pass env nest cons iname ps impln mbody
    = do let impName_in = maybe (mkImpl fc iname ps) id impln
         impName <- inCurrentNS impName_in
         syn <- get Syn
         let [cndata] = lookupName iname (ifaces syn)
             | [] => throw (UndefinedName fc iname)
             | ns => throw (AmbiguousName fc (map fst ns))
         let cn : Name = fst cndata
         let cdata : IFaceInfo = snd cndata
         defs <- get Ctxt

         Just ity <- lookupTyExact cn (gamma defs)
              | Nothing => throw (UndefinedName fc cn)
         Just conty <- lookupTyExact (iconstructor cdata) (gamma defs)
              | Nothing => throw (UndefinedName fc (iconstructor cdata))

         let impsp = nub (concatMap findIBinds ps)

         logTerm 3 ("Found interface " ++ show cn) ity
         log 3 $ " with params: " ++ show (params cdata)
                 ++ " and parents: " ++ show (parents cdata)
                 ++ " using implicits: " ++ show impsp
                 ++ " and methods: " ++ show (methods cdata) ++ "\n"
                 ++ "Constructor: " ++ show (iconstructor cdata) ++ "\n"
         logTerm 3 "Constructor type: " conty
         log 5 $ "Making implementation " ++ show impName

         -- 1. Build the type for the implementation
         -- Make the constraints auto implicit arguments, which can be explicitly
         -- given when using named implementations
         --    (cs : Constraints) -> Impl params
         -- Don't make it a hint if it's a named implementation
         let opts = maybe [Inline, Hint True] (const [Inline]) impln

         let initTy = bindConstraints fc AutoImplicit cons 
                         (apply (IVar fc iname) ps)
         let paramBinds = findBindableNames True vars [] initTy
         let impTy = doBind paramBinds initTy

         let impTyDecl = IClaim fc RigW vis opts (MkImpTy fc impName impTy)
         log 5 $ "Implementation type: " ++ show impTy

         when (typePass pass) $ processDecl [] nest env impTyDecl
         
         -- If the body is empty, we're done for now (just declaring that
         -- the implementation exists and define it later)
         when (defPass pass) $ maybe (pure ())
           (\body_in => do
               -- 1.5. Lookup default definitions and add them to to body
               let (body, missing)
                     = addDefaults fc (map (dropNS . fst) (methods cdata)) 
                                      (defaults cdata) body_in

               log 5 $ "Added defaults: body is " ++ show body
               log 5 $ "Missing methods: " ++ show missing


               -- 2. Elaborate top level function types for this interface
               defs <- get Ctxt
               fns <- topMethTypes [] impName impsp (params cdata)
                                      (map fst (methods cdata)) 
                                      (methods cdata)
               traverse (processDecl [] nest env) (map mkTopMethDecl fns)

               -- 3. Build the record for the implementation
               let mtops = map (Basics.fst . snd) fns
               let con = iconstructor cdata
               let ilhs = impsApply (IVar fc impName) 
                                    (map (\x => (UN x, IBindVar fc x)) impsp)
               -- RHS is the constructor applied to a search for the necessary
               -- parent constraints, then the method implementations
               defs <- get Ctxt
               let fldTys = getFieldArgs !(normaliseHoles defs [] conty)
               log 5 $ "Field types " ++ show fldTys
               let irhs = apply (IVar fc con)
                                (map (const (ISearch fc 500)) (parents cdata)
                                 ++ map (mkMethField impsp fldTys) fns)
               let impFn = IDef fc impName [PatClause fc ilhs irhs]
               log 5 $ "Implementation record: " ++ show impFn
               traverse (processDecl [] nest env) [impFn]
               setFlag fc impName TCInline

               -- 4. (TODO: Order method bodies to be in declaration order, in
               --    case of dependencies)

               -- 5. Elaborate the method bodies

               -- If it's a named implementation, add it as a global hint while
               -- elaborating the bodies
               defs <- get Ctxt
               let hs = openHints defs
               maybe (pure ()) (\x => addOpenHint impName) impln

               body' <- traverse (updateBody (map methNameUpdate fns)) body
               log 10 $ "Implementation body: " ++ show body'
               traverse (processDecl [] nest env) body'
               -- Reset the open hints (remove the named implementation)
               setOpenHints hs
               pure ()) mbody
  where
    -- For the method fields in the record, get the arguments we need to abstract
    -- over
    getFieldArgs : Term vs -> List (Name, List (Name, RigCount, PiInfo))
    getFieldArgs (Bind _ x (Pi c p ty) sc)
        = (x, getArgs ty) :: getFieldArgs sc
      where
        getArgs : Term vs' -> List (Name, RigCount, PiInfo)
        getArgs (Bind _ x (Pi c p _) sc)
            = (x, c, p) :: getArgs sc
        getArgs _ = []
    getFieldArgs _ = []

    impsApply : RawImp -> List (Name, RawImp) -> RawImp
    impsApply fn [] = fn
    impsApply fn ((n, arg) :: ns) 
        = impsApply (IImplicitApp fc fn (Just n) arg) ns

    mkLam : List (Name, RigCount, PiInfo) -> RawImp -> RawImp
    mkLam [] tm = tm
    mkLam ((x, c, p) :: xs) tm 
        = ILam fc c p (Just x) (Implicit fc False) (mkLam xs tm)

    applyTo : FC -> RawImp -> List (Name, RigCount, PiInfo) -> RawImp
    applyTo fc tm [] = tm
    applyTo fc tm ((x, c, Explicit) :: xs)
        = applyTo fc (IApp fc tm (IVar fc x)) xs
    applyTo fc tm ((x, c, AutoImplicit) :: xs)
        = applyTo fc (IImplicitApp fc tm Nothing (IVar fc x)) xs
    applyTo fc tm ((x, c, Implicit) :: xs)
        = applyTo fc (IImplicitApp fc tm (Just x) (IVar fc x)) xs

    -- When applying the method in the field for the record, eta expand
    -- the expected arguments based on the field type, so that implicits get 
    -- inserted in the right place
    mkMethField : List String -> List (Name, List (Name, RigCount, PiInfo)) -> 
                  (Name, Name, List (String, String), RawImp) -> RawImp
    mkMethField impsp fldTys (topn, n, upds, ty)
        = let argns = map applyUpdate (maybe [] id (lookup (dropNS topn) fldTys))
              imps = nub (filter (\n => n `elem` impsp) (findIBinds ty)) in
              -- Pass through implicit arguments to the function which are also
              -- implicit arguments to the declaration
              mkLam argns
                    (impsApply
                         (applyTo fc (IVar fc n) argns)
                         (map (\n => (UN n, IVar fc (UN n))) imps))
      where
        applyUpdate : (Name, RigCount, PiInfo) -> (Name, RigCount, PiInfo)
        applyUpdate (UN n, c, p) 
            = maybe (UN n, c, p) (\n' => (UN n', c, p)) (lookup n upds)
        applyUpdate t = t

    methName : Name -> Name
    methName (NS _ n) = methName n
    methName n 
        = DN (show n) (UN (show n ++ "_" ++ show iname ++ "_" ++
                     maybe "" show impln ++ "_" ++
                     showSep "_" (map show ps)))
    
    applyCon : Name -> Name -> Core (Name, RawImp)
    applyCon impl n 
        = do mn <- inCurrentNS (methName n)
             pure (dropNS n, IVar fc mn)
    
    -- Return method name, specialised method name, implicit name updates,
    -- and method type. Also return how the method name should be updated
    -- in later method types (specifically, putting implicits in)
    topMethType : List (Name, RawImp) ->
                  Name -> List String -> List Name -> List Name ->
                  (Name, (Bool, RawImp)) -> 
                  Core ((Name, Name, List (String, String), RawImp),
                           List (Name, RawImp))   
    topMethType methupds impName impsp pnames allmeths (mn, (d, mty_in))
        = do -- Get the specialised type by applying the method to the
             -- parameters
             n <- inCurrentNS (methName mn)

             -- Avoid any name clashes between parameters and method types by
             -- renaming IBindVars in the method types which appear in the
             -- parameters
             let upds' = !(traverse (applyCon impName) allmeths)
             let mty_in = substNames vars upds' mty_in
             let (mty_in, upds) = runState (renameIBinds impsp (findImplicits mty_in) mty_in) []
             -- Finally update the method type so that implicits from the
             -- parameters are passed through to any earlier methods which
             -- appear in the type
             let mty_in = substNames vars methupds mty_in
             let mbase = bindConstraints fc AutoImplicit cons $
                         substNames vars (zip pnames ps) mty_in
             let ibound = findImplicits mbase

             mty <- bindTypeNamesUsed ibound vars mbase

             log 3 $ "Method " ++ show mn ++ " ==> " ++
                     show n ++ " : " ++ show mty
             log 5 $ "Updates " ++ show methupds
             log 5 $ "From " ++ show mbase 
             log 3 $ "Name updates " ++ show upds 
             log 3 $ "Param names: " ++ show pnames 
             log 10 $ "Used names " ++ show ibound
             let ibinds = nub $ findIBinds mty
             let methupds' = if isNil ibinds then []
                             else [(n, impsApply (IVar fc n)
                                     (map (\x => (UN x, IBindVar fc x)) ibinds))]
             pure ((mn, n, upds, mty), methupds')
    
    topMethTypes : List (Name, RawImp) ->
                   Name -> List String -> List Name -> List Name ->
                   List (Name, (Bool, RawImp)) -> 
                   Core (List (Name, Name, List (String, String), RawImp))
    topMethTypes upds impName impsp pnames allmeths [] = pure []
    topMethTypes upds impName impsp pnames allmeths (m :: ms)
        = do (m', newupds) <- topMethType upds impName impsp pnames allmeths m
             ms' <- topMethTypes (newupds ++ upds) impName impsp pnames allmeths ms
             pure (m' :: ms')

    mkTopMethDecl : (Name, Name, List (String, String), RawImp) -> ImpDecl
    mkTopMethDecl (mn, n, upds, mty) 
        = IClaim fc RigW vis [] (MkImpTy fc n mty)

    -- Given the method type (result of topMethType) return the mapping from
    -- top level method name to current implementation's method name
    methNameUpdate : (Name, Name, t) -> (Name, Name)
    methNameUpdate (mn, fn, _) = (UN (nameRoot mn), fn)

    findMethName : List (Name, Name) -> FC -> Name -> Core Name
    findMethName ns fc n
        = case lookup n ns of
               Nothing => throw (GenericMsg fc 
                                (show n ++ " is not a method of " ++ 
                                 show iname))
               Just n' => pure n'

    updateApp : List (Name, Name) -> RawImp -> Core RawImp
    updateApp ns (IVar fc n)
        = do n' <- findMethName ns fc n
             pure (IVar fc n')
    updateApp ns (IApp fc f arg)
        = do f' <- updateApp ns f
             pure (IApp fc f' arg)
    updateApp ns (IImplicitApp fc f x arg)
        = do f' <- updateApp ns f
             pure (IImplicitApp fc f' x arg)
    updateApp ns tm
        = throw (GenericMsg (getFC tm) "Invalid method definition")

    updateClause : List (Name, Name) -> ImpClause -> 
                   Core ImpClause
    updateClause ns (PatClause fc lhs rhs) 
        = do lhs' <- updateApp ns lhs
             pure (PatClause fc lhs' rhs)
    updateClause ns (WithClause fc lhs wval cs)
        = do lhs' <- updateApp ns lhs
             cs' <- traverse (updateClause ns) cs
             pure (WithClause fc lhs' wval cs')
    updateClause ns (ImpossibleClause fc lhs)
        = do lhs' <- updateApp ns lhs
             pure (ImpossibleClause fc lhs')

    updateBody : List (Name, Name) -> ImpDecl -> Core ImpDecl
    updateBody ns (IDef fc n cs) 
        = do cs' <- traverse (updateClause ns) cs
             n' <- findMethName ns fc n
             pure (IDef fc n' cs')
    updateBody ns _ 
        = throw (GenericMsg fc 
                   "Implementation body can only contain definitions")
