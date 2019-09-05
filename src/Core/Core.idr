module Core.Core

import Core.Env
import Core.TT
import Parser.Support

import public Control.Catchable
import public IdrisJvm.Data.IORef
import IdrisJvm.IO
import IdrisJvm.File
import IdrisJvm.System

%default covering

public export
data TTCErrorMsg
    = FormatOlder
    | FormatNewer
    | EndOfBuffer String
    | Corrupt String

public export
data CaseError = DifferingArgNumbers
               | DifferingTypes
               | MatchErased (vars ** (Env Term vars, Term vars))
               | UnknownType

-- All possible errors, carrying a location
public export
data Error
    = Fatal Error -- flag as unrecoverable (so don't postpone awaiting further info)
    | CantConvert FC (Env Term vars) (Term vars) (Term vars)
    | CantSolveEq FC (Env Term vars) (Term vars) (Term vars)
    | PatternVariableUnifies FC (Env Term vars) Name (Term vars)
    | CyclicMeta FC Name
    | WhenUnifying FC (Env Term vars) (Term vars) (Term vars) Error
    | ValidCase FC (Env Term vars) (Either (Term vars) Error)
    | UndefinedName FC Name
    | InvisibleName FC Name (Maybe (List String))
    | BadTypeConType FC Name
    | BadDataConType FC Name Name
    | NotCovering FC Name Covering
    | NotTotal FC Name PartialReason
    | LinearUsed FC Nat Name
    | LinearMisuse FC Name RigCount RigCount
    | BorrowPartial FC (Env Term vars) (Term vars) (Term vars)
    | BorrowPartialType FC (Env Term vars) (Term vars)
    | AmbiguousName FC (List Name)
    | AmbiguousElab FC (Env Term vars) (List (Term vars))
    | AmbiguousSearch FC (Env Term vars) (List (Term vars))
    | AllFailed (List (Maybe Name, Error))
    | RecordTypeNeeded FC (Env Term vars)
    | NotRecordField FC String (Maybe Name)
    | NotRecordType FC Name
    | IncompatibleFieldUpdate FC (List String)
    | InvalidImplicits FC (Env Term vars) (List (Maybe Name)) (Term vars)
    | TryWithImplicits FC (Env Term vars) (List (Name, Term vars))
    | BadUnboundImplicit FC (Env Term vars) Name (Term vars)
    | CantSolveGoal FC (Env Term vars) (Term vars)
    | DeterminingArg FC Name Int (Env Term vars) (Term vars)
    | UnsolvedHoles (List (FC, Name))
    | CantInferArgType FC (Env Term vars) Name Name (Term vars)
    | SolvedNamedHole FC (Env Term vars) Name (Term vars)
    | VisibilityError FC Visibility Name Visibility Name
    | NonLinearPattern FC Name
    | BadPattern FC Name
    | NoDeclaration FC Name
    | AlreadyDefined FC Name
    | NotFunctionType FC (Env Term vars) (Term vars)
    | RewriteNoChange FC (Env Term vars) (Term vars) (Term vars)
    | NotRewriteRule FC (Env Term vars) (Term vars)
    | CaseCompile FC Name CaseError
    | MatchTooSpecific FC (Env Term vars) (Term vars)
    | BadDotPattern FC (Env Term vars) String (Term vars) (Term vars)
    | BadImplicit FC String
    | BadRunElab FC (Env Term vars) (Term vars)
    | GenericMsg FC String
    | TTCError TTCErrorMsg
    | FileErr String FileError
    | ParseFail FC ParseError
    | ModuleNotFound FC (List String)
    | CyclicImports (List (List String))
    | ForceNeeded
    | InternalError String

    | InType FC Name Error
    | InCon FC Name Error
    | InLHS FC Name Error
    | InRHS FC Name Error

export
Show TTCErrorMsg where
  show FormatOlder = "TTC data is in an older format"
  show FormatNewer = "TTC data is in a newer format"
  show (EndOfBuffer when) = "End of buffer when reading " ++ when
  show (Corrupt ty) = "Corrupt TTC data for " ++ ty

-- Simplest possible display - higher level languages should unelaborate names
-- and display annotations appropriately
export
Show Error where
  show (Fatal err) = show err
  show (CantConvert fc env x y)
      = show fc ++ ":Type mismatch: " ++ show x ++ " and " ++ show y
  show (CantSolveEq fc env x y)
      = show fc ++ ":" ++ show x ++ " and " ++ show y ++ " are not equal"
  show (PatternVariableUnifies fc env n x)
      = show fc ++ ":Pattern variable " ++ show n ++ " unifies with " ++ show x
  show (CyclicMeta fc n)
      = show fc ++ ":Cycle detected in metavariable solution " ++ show n
  show (WhenUnifying fc _ x y err)
      = show fc ++ ":When unifying: " ++ show x ++ " and " ++ show y ++ "\n\t" ++ show err
  show (ValidCase fc _ prob)
      = show fc ++ ":" ++
           case prob of
             Left tm => assert_total (show tm) ++ " is not a valid impossible pattern because it typechecks"
             Right err => "Not a valid impossible pattern:\n\t" ++ assert_total (show err)
  show (UndefinedName fc x) = show fc ++ ":Undefined name " ++ show x
  show (InvisibleName fc x (Just ns))
       = show fc ++ ":Name " ++ show x ++ " is inaccessible since " ++
         showSep "." (reverse ns) ++ " is not explicitly imported"
  show (InvisibleName fc x _) = show fc ++ ":Name " ++ show x ++ " is private"
  show (BadTypeConType fc n)
       = show fc ++ ":Return type of " ++ show n ++ " must be Type"
  show (BadDataConType fc n fam)
       = show fc ++ ":Return type of " ++ show n ++ " must be in " ++ show fam
  show (NotCovering fc n cov)
       = show fc ++ ":" ++ show n ++ " is not covering:\n\t" ++
            case cov of
                 IsCovering => "Oh yes it is (Internal error!)"
                 MissingCases cs => "Missing cases:\n\t" ++
                                           showSep "\n\t" (map show cs)
                 NonCoveringCall ns => "Calls non covering function"
                                           ++ (case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ showSep ", " (map show ns))

  show (NotTotal fc n r)
       = show fc ++ ":" ++ show n ++ " is not total"
  show (LinearUsed fc count n)
      = show fc ++ ":There are " ++ show count ++ " uses of linear name " ++ show n
  show (LinearMisuse fc n exp ctx)
      = show fc ++ ":Trying to use " ++ showRig exp ++ " name " ++ show n ++
                   " in " ++ showRel ctx ++ " context"
     where
       showRig : RigCount -> String
       showRig Rig0 = "irrelevant"
       showRig Rig1 = "linear"
       showRig RigW = "unrestricted"

       showRel : RigCount -> String
       showRel Rig0 = "irrelevant"
       showRel Rig1 = "relevant"
       showRel RigW = "non-linear"
  show (BorrowPartial fc env t arg)
      = show fc ++ ":" ++ show t ++ " borrows argument " ++ show arg ++
                   " so must be fully applied"
  show (BorrowPartialType fc env t)
      = show fc ++ ":" ++ show t ++ " borrows, so must return a concrete type"

  show (AmbiguousName fc ns) = show fc ++ ":Ambiguous name " ++ show ns
  show (AmbiguousElab fc env ts) = show fc ++ ":Ambiguous elaboration " ++ show ts
  show (AmbiguousSearch fc env ts) = show fc ++ ":Ambiguous search " ++ show ts
  show (AllFailed ts) = "No successful elaboration: " ++ assert_total (show ts)
  show (RecordTypeNeeded fc env)
      = show fc ++ ":Can't infer type of record to update"
  show (NotRecordField fc fld Nothing)
      = show fc ++ ":" ++ fld ++ " is not part of a record type"
  show (NotRecordField fc fld (Just ty))
      = show fc ++ ":Record type " ++ show ty ++ " has no field " ++ fld
  show (NotRecordType fc ty)
      = show fc ++ ":" ++ show ty ++ " is not a record type"
  show (IncompatibleFieldUpdate fc flds)
      = show fc ++ ":Field update " ++ showSep "->" flds ++ " not compatible with other updates"
  show (InvalidImplicits fc env ns tm)
     = show fc ++ ":" ++ show ns ++ " are not valid implicit arguments in " ++ show tm
  show (TryWithImplicits fc env imps)
     = show fc ++ ":Need to bind implicits "
          ++ showSep "," (map (\x => show (fst x) ++ " : " ++ show (snd x)) imps)
          ++ "\n(The front end should probably have done this for you. Please report!)"
  show (BadUnboundImplicit fc env n ty)
      = show fc ++ ":Can't bind name " ++ nameRoot n ++
                   " with type " ++ show ty
  show (CantSolveGoal fc env g)
      = show fc ++ ":Can't solve goal " ++ assert_total (show g)
  show (DeterminingArg fc n i env g)
      = show fc ++ ":Can't solve goal " ++ assert_total (show g) ++
                " since argument " ++ show n ++ " can't be inferred"
  show (UnsolvedHoles hs) = "Unsolved holes " ++ show hs
  show (CantInferArgType fc env n h ty)
      = show fc ++ ":Can't infer type for " ++ show n ++
                   " (got " ++ show ty ++ " with hole " ++ show h ++ ")"
  show (SolvedNamedHole fc _ h _) = show fc ++ ":Named hole " ++ show h ++ " is solved by unification"
  show (VisibilityError fc vx x vy y)
      = show fc ++ ":" ++ show vx ++ " " ++ show x ++ " cannot refer to "
                       ++ show vy ++ " " ++ show y
  show (NonLinearPattern fc n) = show fc ++ ":Non linear pattern variable " ++ show n
  show (BadPattern fc n) = show fc ++ ":Pattern not allowed here: " ++ show n
  show (NoDeclaration fc x) = show fc ++ ":No type declaration for " ++ show x
  show (AlreadyDefined fc x) = show fc ++ ":" ++ show x ++ " is already defined"
  show (NotFunctionType fc env tm) = show fc ++ ":Not a function type: " ++ show tm
  show (RewriteNoChange fc env rule ty)
      = show fc ++ ":Rewriting by " ++ show rule ++ " did not change type " ++ show ty
  show (NotRewriteRule fc env rule)
      = show fc ++ ":" ++ show rule ++ " is not a rewrite rule type"
  show (CaseCompile fc n DifferingArgNumbers)
      = show fc ++ ":Patterns for " ++ show n ++ " have different numbers of arguments"
  show (CaseCompile fc n DifferingTypes)
      = show fc ++ ":Patterns for " ++ show n ++ " require matching on different types"
  show (CaseCompile fc n UnknownType)
      = show fc ++ ":Can't infer type to match in " ++ show n
  show (CaseCompile fc n (MatchErased (_ ** (env, tm))))
      = show fc ++ ":Attempt to match on erased argument " ++ show tm ++
                   " in " ++ show n
  show (MatchTooSpecific fc env tm)
      = show fc ++ ":Can't match on " ++ show tm ++ " as it is has a polymorphic type"
  show (BadDotPattern fc env reason x y)
      = show fc ++ ":Can't match on " ++ show x ++
           (if reason /= "" then " (" ++ reason ++ ")" else "") ++
           " - it elaborates to " ++ show y
  show (BadImplicit fc str) = show fc ++ ":" ++ str ++ " can't be bound here"
  show (BadRunElab fc env script) = show fc ++ ":Bad elaborator script " ++ show script
  show (GenericMsg fc str) = show fc ++ ":" ++ str
  show (TTCError msg) = "Error in TTC file: " ++ show msg
  show (FileErr fname err) = "File error (" ++ fname ++ "): " ++ show err
  show (ParseFail fc err) = "Parse error (" ++ show err ++ ")"
  show (ModuleNotFound fc ns)
      = show fc ++ ":" ++ showSep "." (reverse ns) ++ " not found"
  show (CyclicImports ns)
      = "Module imports form a cycle: " ++ showSep " -> " (map showMod ns)
    where
      showMod : List String -> String
      showMod ns = showSep "." (reverse ns)
  show ForceNeeded = "Internal error when resolving implicit laziness"
  show (InternalError str) = "INTERNAL ERROR: " ++ str

  show (InType fc n err)
       = show fc ++ ":When elaborating type of " ++ show n ++ ":\n" ++
         show err
  show (InCon fc n err)
       = show fc ++ ":When elaborating type of constructor " ++ show n ++ ":\n" ++
         show err
  show (InLHS fc n err)
       = show fc ++ ":When elaborating left hand side of " ++ show n ++ ":\n" ++
         show err
  show (InRHS fc n err)
       = show fc ++ ":When elaborating right hand side of " ++ show n ++ ":\n" ++
         show err

export
getErrorLoc : Error -> Maybe FC
getErrorLoc (Fatal err) = getErrorLoc err
getErrorLoc (CantConvert loc _ _ _) = Just loc
getErrorLoc (CantSolveEq loc _ _ _) = Just loc
getErrorLoc (PatternVariableUnifies loc _ _ _) = Just loc
getErrorLoc (CyclicMeta loc _) = Just loc
getErrorLoc (WhenUnifying loc _ _ _ _) = Just loc
getErrorLoc (ValidCase loc _ _) = Just loc
getErrorLoc (UndefinedName loc _) = Just loc
getErrorLoc (InvisibleName loc _ _) = Just loc
getErrorLoc (BadTypeConType loc _) = Just loc
getErrorLoc (BadDataConType loc _ _) = Just loc
getErrorLoc (NotCovering loc _ _) = Just loc
getErrorLoc (NotTotal loc _ _) = Just loc
getErrorLoc (LinearUsed loc _ _) = Just loc
getErrorLoc (LinearMisuse loc _ _ _) = Just loc
getErrorLoc (BorrowPartial loc _ _ _) = Just loc
getErrorLoc (BorrowPartialType loc _ _) = Just loc
getErrorLoc (AmbiguousName loc _) = Just loc
getErrorLoc (AmbiguousElab loc _ _) = Just loc
getErrorLoc (AmbiguousSearch loc _ _) = Just loc
getErrorLoc (AllFailed ((_, x) :: _)) = getErrorLoc x
getErrorLoc (AllFailed []) = Nothing
getErrorLoc (RecordTypeNeeded loc _) = Just loc
getErrorLoc (NotRecordField loc _ _) = Just loc
getErrorLoc (NotRecordType loc _) = Just loc
getErrorLoc (IncompatibleFieldUpdate loc _) = Just loc
getErrorLoc (InvalidImplicits loc _ _ _) = Just loc
getErrorLoc (TryWithImplicits loc _ _) = Just loc
getErrorLoc (BadUnboundImplicit loc _ _ _) = Just loc
getErrorLoc (CantSolveGoal loc _ _) = Just loc
getErrorLoc (DeterminingArg loc _ _ _ _) = Just loc
getErrorLoc (UnsolvedHoles ((loc, _) :: _)) = Just loc
getErrorLoc (UnsolvedHoles []) = Nothing
getErrorLoc (CantInferArgType loc _ _ _ _) = Just loc
getErrorLoc (SolvedNamedHole loc _ _ _) = Just loc
getErrorLoc (VisibilityError loc _ _ _ _) = Just loc
getErrorLoc (NonLinearPattern loc _) = Just loc
getErrorLoc (BadPattern loc _) = Just loc
getErrorLoc (NoDeclaration loc _) = Just loc
getErrorLoc (AlreadyDefined loc _) = Just loc
getErrorLoc (NotFunctionType loc _ _) = Just loc
getErrorLoc (RewriteNoChange loc _ _ _) = Just loc
getErrorLoc (NotRewriteRule loc _ _) = Just loc
getErrorLoc (CaseCompile loc _ _) = Just loc
getErrorLoc (MatchTooSpecific loc _ _) = Just loc
getErrorLoc (BadDotPattern loc _ _ _ _) = Just loc
getErrorLoc (BadImplicit loc _) = Just loc
getErrorLoc (BadRunElab loc _ _) = Just loc
getErrorLoc (GenericMsg loc _) = Just loc
getErrorLoc (TTCError _) = Nothing
getErrorLoc (FileErr _ _) = Nothing
getErrorLoc (ParseFail loc _) = Just loc
getErrorLoc (ModuleNotFound loc _) = Just loc
getErrorLoc (CyclicImports _) = Nothing
getErrorLoc ForceNeeded = Nothing
getErrorLoc (InternalError _) = Nothing
getErrorLoc (InType _ _ err) = getErrorLoc err
getErrorLoc (InCon _ _ err) = getErrorLoc err
getErrorLoc (InLHS _ _ err) = getErrorLoc err
getErrorLoc (InRHS _ _ err) = getErrorLoc err

-- Core is a wrapper around JVM_IO that is specialised for efficiency.
export
record Core t where
  constructor MkCore
  runCore : JVM_IO (Either Error t)

export
coreRun : Core a ->
          (Error -> JVM_IO b) -> (a -> JVM_IO b) -> JVM_IO b
coreRun (MkCore act) err ok
    = either err ok !act

export
coreFail : Error -> Core a
coreFail e = MkCore (pure (Left e))

export
wrapError : (Error -> Error) -> Core a -> Core a
wrapError fe (MkCore prog)
    = MkCore (prog >>=
                 (\x => case x of
                             Left err => pure (Left (fe err))
                             Right val => pure (Right val)))

-- This would be better if we restrict it to a limited set of JVM_IO operations
export
%inline
coreLift : JVM_IO a -> Core a
coreLift op = MkCore (do op' <- op
                         pure (Right op'))

{- Monad, Applicative, Traversable are specialised by hand for Core.
In theory, this shouldn't be necessary, but it turns out that Idris 1 doesn't
specialise interfaces under 'case' expressions, and this has a significant
impact on both compile time and run time.

Of course it would be a good idea to fix this in Idris, but it's not an urgent
thing on the road to self hosting, and we can make sure this isn't a problem
in the next version (i.e., in this project...)! -}

-- Functor (specialised)
export %inline
map : (a -> b) -> Core a -> Core b
map f (MkCore a) = MkCore (map (map f) a)

-- Monad (specialised)
export %inline
(>>=) : Core a -> (a -> Core b) -> Core b
(>>=) (MkCore act) f
    = MkCore (act >>=
                   (\x => case x of
                               Left err => pure (Left err)
                               Right val => runCore (f val)))

-- Applicative (specialised)
export %inline
pure : a -> Core a
pure x = MkCore (pure (pure x))

export
(<*>) : Core (a -> b) -> Core a -> Core b
(<*>) (MkCore f) (MkCore a) = MkCore [| f <*> a |]

export %inline
when : Bool -> Lazy (Core ()) -> Core ()
when True f = f
when False f = pure ()

export
Catchable Core Error where
  catch (MkCore prog) h
      = MkCore ( do p' <- prog
                    case p' of
                         Left e => let MkCore he = h e in he
                         Right val => pure (Right val))
  throw = coreFail

-- Traversable (specialised)
traverse' : (a -> Core b) -> List a -> List b -> Core (List b)
traverse' f [] acc = pure (reverse acc)
traverse' f (x :: xs) acc
    = traverse' f xs (!(f x) :: acc)

export
traverse : (a -> Core b) -> List a -> Core (List b)
traverse f xs = traverse' f xs []

export
traverseOpt : (a -> Core b) -> Maybe a -> Core (Maybe b)
traverseOpt f Nothing = pure Nothing
traverseOpt f (Just x) = map Just (f x)

export
traverse_ : (a -> Core b) -> List a -> Core ()
traverse_ f [] = pure ()
traverse_ f (x :: xs)
    = do f x
         traverse_ f xs

namespace Binder
  export
  traverse : (a -> Core b) -> Binder a -> Core (Binder b)
  traverse f (Lam c p ty) = pure $ Lam c p !(f ty)
  traverse f (Let c val ty) = pure $ Let c !(f val) !(f ty)
  traverse f (Pi c p ty) = pure $ Pi c p !(f ty)
  traverse f (PVar c p ty) = pure $ PVar c p !(f ty)
  traverse f (PLet c val ty) = pure $ PLet c !(f val) !(f ty)
  traverse f (PVTy c ty) = pure $ PVTy c !(f ty)

export
anyM : (a -> Core Bool) -> List a -> Core Bool
anyM f [] = pure False
anyM f (x :: xs)
    = if !(f x)
         then pure True
         else anyM f xs

export
allM : (a -> Core Bool) -> List a -> Core Bool
allM f [] = pure True
allM f (x :: xs)
    = if !(f x)
         then allM f xs
         else pure False

export
filterM : (a -> Core Bool) -> List a -> Core (List a)
filterM p [] = pure []
filterM p (x :: xs)
    = if !(p x)
         then do xs' <- filterM p xs
                 pure (x :: xs')
         else filterM p xs

export
data Ref : label -> Type -> Type where
	   MkRef : IORef a -> Ref x a

export
newRef : (x : label) -> t -> Core (Ref x t)
newRef x val
    = do ref <- coreLift (newIORef val)
         pure (MkRef ref)

export %inline
get : (x : label) -> {auto ref : Ref x a} -> Core a
get x {ref = MkRef io} = coreLift (readIORef io)

export %inline
put : (x : label) -> {auto ref : Ref x a} -> a -> Core ()
put x {ref = MkRef io} val = coreLift (writeIORef io val)

export
cond : List (Lazy Bool, Lazy a) -> a -> a
cond [] def = def
cond ((x, y) :: xs) def = if x then y else cond xs def

export
condC : List (Core Bool, Core a) -> Core a -> Core a
condC [] def = def
condC ((x, y) :: xs) def
    = if !x then y else condC xs def

