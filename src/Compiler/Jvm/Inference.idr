module Compiler.Jvm.Inference

import Data.SortedMap

import Compiler.Jvm.Asm
import Compiler.Jvm.InferredType

%access public export

inferConstant : Constant -> InferredType
inferConstant (I x) = IInt
inferConstant (BI x) = inferredBigIntegerType
inferConstant (Str x) = inferredStringType
inferConstant (Ch x) = IChar
inferConstant (Db x) = IDouble
inferConstant WorldVal = IInt
inferConstant IntType = IInt
inferConstant IntegerType = IInt
inferConstant StringType = IInt
inferConstant CharType = IInt
inferConstant DoubleType = IInt
inferConstant WorldType = IInt

record InferenceState where
    constructor MkInferenceState
    currentFunctionInference : InferredVariables
    functionTypes : InferredFunctionTypes
    caseCounter: Int
    lambdaCounter: Int

InferredExpressionType : Type
InferredExpressionType = (InferredType, InferenceState)

addVarType : Nat -> InferredType -> InferenceState -> InferenceState
addVarType var ty state = record {currentFunctionInference $= (SortedMap.insert var ty)} state

getVarType : Nat -> InferenceState -> InferredType
getVarType var state = fromMaybe inferredObjectType $ SortedMap.lookup var (currentFunctionInference state)

getFunctionType : Jname -> InferenceState -> InferredFunctionType
getFunctionType name state = fromMaybe (MkInferredFunctionType inferredObjectType SortedMap.empty) $
    SortedMap.lookup name (functionTypes state)

parameters (c : Ref Ctxt Defs,
            defs: Defs)
    mutual
        inferConAlt : InferenceState -> Int -> Jvars vars -> Nat -> CConAlt vars -> Core InferredExpressionType
        inferConAlt {vars} state i vs idrisObj (MkConAlt n tag args sc) = inferExp i vs sc

        inferConstAlt : InferenceState -> Int -> Jvars vars -> CConstAlt vars -> Core InferenceState
        inferConstAlt state i vs (MkConstAlt c exp) = inferExp i vs exp

        -- oops, no traverse for Vect in Core
        inferArgs : InferenceState -> Vect n (CExp vars) -> Core InferredExpressionType
        inferArgs state [] = pure state
        inferArgs state (arg :: args) = inferArgs (!(inferExp state arg)) args

        export
        inferExp : InferenceState -> Int -> Jvars vars -> CExp vars -> Core InferredExpressionType
        inferExp state i vs (CLocal fc el) =
            let var = jvarIndex $ lookupJvar el vs
            in pure (getVarType var state, state)
        inferExp state i vs (CLam fc x sc) = do
            let vsNew = extendJvars i [x] vs
            (lambdaReturnType, state) <- inferExp state (i + 1) vsNew sc
            pure $ (inferredLambdaType, state)
        inferExp state i vs (CLet fc x val sc) = do
            let (ty, state) <- inferExp state i vs val
                vsNew = extendJvars i [x] vs
                state = addVarType (cast i) ty state
            in inferExp state i vsNew sc
        inferExp (CApp fc (CRef _ f) args) =
          let loadedArgs = showSep lineSeparator !(traverse (inferExp) args)
              nArgs = length args
              jname = jvmName f
          in pure $ loadedArgs ++ lineSeparator ++ instruction ["call", className jname, methodName jname, show nArgs]
        inferExp (CApp fc f args) =
          let loadedArgs = showSep lineSeparator !(traverse (inferExp) args)
              loadedLambdaVar = instructions [
                  [!(inferExp f)],
                  ["cast", "java/util/function/Function"]
              ]
          in pure $ loadedLambdaVar ++ lineSeparator ++ loadedArgs ++ lineSeparator ++ "applyLambda"
        inferExp (CCon fc name tag args)
          = pure $ inferConstructor name tag !(traverse (inferExp) args)
        inferExp (COp fc op args)
          = pure $ inferOp op !(inferArgs i vs args)
        inferExp (CExtPrim fc p args)
          = inferExtPrim i vs (toPrim p) args
        inferExp (CForce fc t) = pure $ showSep lineSeparator [!(inferExp t), "force"]
        inferExp (CDelay fc t) = pure $ showSep lineSeparator [!(inferExp t), "delay"]
        inferExp (CConCase fc sc alts@(alt::_) def)
          = do tcode <- inferExp (i+1) vs sc
               defc <- maybe (pure Nothing) (\v => pure (Just !(inferExp v))) def
               let idrisObj = MkJvar ("sc" ++ show i) (cast i)
               let idrisObjIndex = jvarIndex idrisObj
               let idrisObjClass = constructorClass alt
               pure $ instructions [
                  [astore fc idrisObj tcode],
                  ["aload", show idrisObjIndex],
                  ["field", "get", idrisObjClass, "constructorId", "I"],
                  ["lookupSwitch"],
                  [showSep lineSeparator !(traverse (inferConAlt (i+1) vs idrisObjIndex) alts)],
                  [inferCaseDef defc],
                  ["endLookupSwitch"]
              ]
        inferExp (CConstCase fc sc alts def)
          = do defc <- maybe (pure Nothing) (\v => pure (Just !(inferExp v))) def
               tcode <- inferExp (i+1) vs sc
               let ifExpr = MkJvar ("if" ++ show i) (cast i)
               pure $ instructions [
                  [astore fc ifExpr tcode],
                  ["if"],
                  [showSep lineSeparator !(traverse (inferConstAlt (i+1) vs (jvarIndex ifExpr)) alts)],
                  [inferCaseDef defc],
                  ["endIf"]
               ]
        inferExp (CPrimVal fc c) = pure $ inferConstant inferString c
        inferExp (CErased fc) = pure "erased"
        inferExp (CCrash fc msg) = pure $ "error " ++ show msg ++ ")"
        inferExp expr = pure $ "error " ++ show expr

        inferDef : {auto c : Ref Ctxt Defs} -> Name -> CDef -> Core (SortedMap Jname (List Jname))
        inferDef n (MkFun args exp) = inferExp exp
        inferDef n _ = deps

        infer : Name -> Core InferenceState
        infer name =
            case !(lookupCtxtExact name (gamma defs)) of
               Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
               Just d => case compexpr d of
                  Nothing => throw (InternalError ("No compiled definition for " ++ show n))
                  Just d => do
                    let jname = jvmName name
                    let functionType = MkInferredFunctionType inferredObjectType SortedMap.empty
                    let newFunctionTypes = SortedMap.insert jname functionType
                                                (functionTypes state)
                        newState = record {functionTypes $= SortedMap.insert jname functionType} state
                    inferDef newState name d

