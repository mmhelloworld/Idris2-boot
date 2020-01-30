module Compiler.Jvm.FunctionTree

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name

import Compiler.Jvm.Tree

import Data.SortedSet
import Data.Vect

%access public export

parameters (c : Ref Ctxt Defs,
            defs: Defs)
    mutual

        buildFunctionTreeConAlt : List (Tree Name) -> SortedSet Name -> List (CConAlt vars) -> Core (SortedSet Name, List (Tree Name))
        buildFunctionTreeConAlt acc visited [] = pure (visited, acc)
        buildFunctionTreeConAlt acc visited ((MkConAlt n tag args sc) :: alts) = do
            (visited, newAcc) <- buildFunctionTreeExp acc visited sc
            buildFunctionTreeConAlt newAcc visited alts

        buildFunctionTreeConstAlt : List (Tree Name) -> SortedSet Name -> List (CConstAlt vars) -> Core (SortedSet Name, List (Tree Name))
        buildFunctionTreeConstAlt acc visited [] = pure (visited, acc)
        buildFunctionTreeConstAlt acc visited ((MkConstAlt c exp) :: alts) = do
            (visited, newAcc) <- buildFunctionTreeExp acc visited exp
            buildFunctionTreeConstAlt newAcc visited alts

        buildFunctionTreeArgs : List (Tree Name) -> SortedSet Name -> Vect n (CExp vars) -> Core (SortedSet Name, List (Tree Name))
        buildFunctionTreeArgs acc visited [] = pure (visited, acc)
        buildFunctionTreeArgs acc visited (arg :: args) = do
            (visited, newAcc) <- buildFunctionTreeExp acc visited arg
            buildFunctionTreeArgs newAcc visited args

        buildFunctionTreeCApp : List (Tree Name) -> SortedSet Name -> List (CExp vars) -> Core (SortedSet Name, List (Tree Name))
        buildFunctionTreeCApp acc visited [] = pure (visited, acc)
        buildFunctionTreeCApp acc visited (arg :: args) = do
            (visited, newAcc) <- buildFunctionTreeExp acc visited arg
            buildFunctionTreeCApp newAcc visited args

        buildFunctionTreeExp : List (Tree Name) -> SortedSet Name -> CExp vars -> Core (SortedSet Name, List (Tree Name))
        buildFunctionTreeExp acc visited (CLocal fc el) = pure (visited, acc)
        buildFunctionTreeExp acc visited (CLam fc x sc) = buildFunctionTreeExp acc visited sc
        buildFunctionTreeExp acc visited (CLet fc x val sc) = do
            (visited, valAcc) <- buildFunctionTreeExp acc visited val
            buildFunctionTreeExp valAcc visited sc
        buildFunctionTreeExp acc visited (CApp fc (CRef _ f) args) = do
            (visited, newAcc) <- buildFunctionTreeCApp acc visited args
            if SortedSet.contains f visited then
                pure (visited, newAcc)
            else do
                (visited, child) <- buildFunctionTree visited f
                pure (visited, child :: newAcc)
        buildFunctionTreeExp acc visited (CApp fc f args) = do
            (visited, newAcc) <- buildFunctionTreeCApp acc visited args
            buildFunctionTreeExp newAcc visited f
        buildFunctionTreeExp acc visited (CCon fc name tag args) = buildFunctionTreeCApp acc visited args
        buildFunctionTreeExp acc visited (COp fc op args) = buildFunctionTreeArgs acc visited args
        buildFunctionTreeExp acc visited (CExtPrim fc p args) = buildFunctionTreeCApp acc visited args
        buildFunctionTreeExp acc visited (CForce fc t) = buildFunctionTreeExp acc visited t
        buildFunctionTreeExp acc visited (CDelay fc t) = buildFunctionTreeExp acc visited t
        buildFunctionTreeExp acc visited (CConCase fc sc alts def)
            = do (visited, accSc) <- buildFunctionTreeExp acc visited sc
                 (visited, accDefc) <- maybe (pure (visited, accSc)) (\v => pure !(buildFunctionTreeExp accSc visited v)) def
                 buildFunctionTreeConAlt accDefc visited alts
        buildFunctionTreeExp acc visited (CConstCase fc sc alts def)
            = do (visited, accDefc) <- maybe (pure (visited, acc)) (\v => pure !(buildFunctionTreeExp acc visited v)) def
                 (visited, accSc) <- buildFunctionTreeExp accDefc visited sc
                 buildFunctionTreeConstAlt accSc visited alts
        buildFunctionTreeExp acc visited (CPrimVal fc c) = pure (visited, acc)
        buildFunctionTreeExp acc visited (CErased fc) = pure (visited, acc)
        buildFunctionTreeExp acc visited (CCrash fc msg) = pure (visited, acc)
        buildFunctionTreeExp acc visited expr = pure (visited, acc)

        buildFunctionTreeDef : SortedSet Name -> Name -> CDef -> Core (SortedSet Name, List (Tree Name))
        buildFunctionTreeDef visited n (MkFun args exp) = buildFunctionTreeExp [] visited exp
        buildFunctionTreeDef visited n (MkError exp) = buildFunctionTreeExp [] visited exp
        buildFunctionTreeDef visited n (MkForeign _ _ _) = pure (visited, [])
        buildFunctionTreeDef visited n (MkCon t a) = pure (visited, [])

        buildFunctionTree : SortedSet Name -> Name -> Core (SortedSet Name, Tree Name)
        buildFunctionTree visited name =
            case !(lookupCtxtExact name (gamma defs)) of
               Nothing => throw (InternalError ("Undefined name " ++ show name))
               Just d => case compexpr d of
                  Nothing => throw (InternalError ("No compiled definition for " ++ show name))
                  Just d => do
                    (visited, children) <- buildFunctionTreeDef (SortedSet.insert name visited) name d
                    pure $ (visited, Node name children)

buildFunctionTreeMain : {auto c : Ref Ctxt Defs} -> Defs -> Core (Tree Name)
buildFunctionTreeMain {c} defs = pure . snd $ !(buildFunctionTree c defs SortedSet.empty (NS ["Main"] (UN "main")))