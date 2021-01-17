module Compiler.Jvm.Optimizer

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.Bool.Extra
import Data.SortedMap
import Data.SortedSet
import Data.Vect

import Compiler.Jvm.InferredType
import Compiler.Jvm.Jname
import Compiler.Jvm.Asm
import Compiler.Jvm.ExtPrim
import Compiler.Jvm.ShowUtil
import Compiler.Jvm.Foreign

mutual
    hasTailCall : (predicate: Name -> Bool) -> NamedCExp -> Bool
    hasTailCall predicate (NmLet _ _ _ expr) = hasTailCall predicate expr
    hasTailCall predicate (NmApp _ (NmRef _ name) _) = predicate name
    hasTailCall predicate (NmApp _ lambdaVariable _) = predicate (UN "")
    hasTailCall predicate (NmExtPrim fc p args) = predicate (UN "")
    hasTailCall predicate (NmConCase _ _ conAlts def) =
        maybe False (\defExp => hasTailCall predicate defExp) def || hasTailCallConAlt predicate conAlts
    hasTailCall predicate (NmConstCase _ _ constAlts def) =
        maybe False (\defExp => hasTailCall predicate defExp) def || hasTailCallConstAlt predicate constAlts
    hasTailCall _ _ = False

    hasTailCallConAlt : (predicate: Name -> Bool) -> List NamedConAlt -> Bool
    hasTailCallConAlt predicate [] = False
    hasTailCallConAlt predicate ((MkNConAlt _ _ _ expr) :: alts) =
        hasTailCall predicate expr || hasTailCallConAlt predicate alts

    hasTailCallConstAlt : (predicate: Name -> Bool) -> List NamedConstAlt -> Bool
    hasTailCallConstAlt predicate [] = False
    hasTailCallConstAlt predicate ((MkNConstAlt _ expr) :: alts) =
        hasTailCall predicate expr || hasTailCallConstAlt predicate alts

thunkExpr : NamedCExp -> NamedCExp
thunkExpr expr = NmLam (getFC expr) (UN "$jvm$thunk") expr

export
tySpec : NamedCExp -> Asm InferredType
tySpec (NmCon fc (UN "Int") _ []) = pure IInt
tySpec (NmCon fc (UN "Integer") _ []) = pure inferredBigIntegerType
tySpec (NmCon fc (UN "String") _ []) = pure inferredStringType
tySpec (NmCon fc (UN "Double") _ []) = pure IDouble
tySpec (NmCon fc (UN "Char") _ []) = pure IChar
tySpec (NmCon fc (UN "Bool") _ []) = pure IBool
tySpec (NmCon fc (UN "void") _ []) = pure IVoid
tySpec (NmCon fc (UN ty) _ []) = pure $ IRef ty
tySpec (NmCon fc (NS _ n) _ [])
     = cond [(n == UN "Unit", pure IVoid)]
          (pure inferredObjectType)
tySpec ty = pure inferredObjectType

export
getFArgs : NamedCExp -> Asm (List (NamedCExp, NamedCExp))
getFArgs (NmCon fc _ (Just 0) _) = pure []
getFArgs (NmCon fc _ (Just 1) [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
getFArgs arg = Throw (getFC arg) ("Badly formed jvm call argument list " ++ show arg)

getLineNumbers : FilePos -> FilePos -> (Int, Int)
getLineNumbers (lineStart, _) (lineEnd, colEnd) =
    (lineStart + 1, if colEnd == 1 then lineEnd else lineEnd + 1)

export
getSourceLocation : NamedCExp -> (String, Int, Int)
getSourceLocation expr = case getFC expr of
    EmptyFC => case expr of
        (NmExtPrim _ _ (arg :: args)) => getSourceLocation arg
        (NmOp _ _ (arg :: _)) => getSourceLocation arg
        _ => ("Main.idr", 1, 1)
    (MkFC fileName startPos endPos) =>
        (fileName, getLineNumbers startPos endPos)

export
getSourceLocationFromFc : FC -> (String, Int, Int)
getSourceLocationFromFc EmptyFC = ("Main.idr", 1, 1)
getSourceLocationFromFc (MkFC fileName startPos endPos) = (fileName, getLineNumbers startPos endPos)

mutual
    export
    used : String -> NamedCExp -> Bool
    used n (NmLocal fc var) = n == jvmSimpleName var
    used n (NmRef _ _) = False
    used n (NmLam _ param sc) = n == jvmSimpleName param || used n sc
    used n (NmLet _ var value sc) = n == jvmSimpleName var || used n value || used n sc
    used n (NmApp _ f args) = used n f || anyTrue (map (used n) args)
    used n (NmCon _ _ _ args) = anyTrue (map (used n) args)
    used n (NmOp _ _ args) = anyTrue (toList (map (used n) args))
    used n (NmExtPrim _ _ args) = anyTrue (map (used n) args)
    used n (NmForce _ t) = used n t
    used n (NmDelay _ t) = used n t
    used n (NmConCase _ sc alts def)
        = used n sc || anyTrue (map (usedCon n) alts)
              || maybe False (used n) def
    used n (NmConstCase _ sc alts def)
        = used n sc || anyTrue (map (usedConst n) alts)
              || maybe False (used n) def
    used n _ = False

    usedCon : String -> NamedConAlt -> Bool
    usedCon n (MkNConAlt _ _ _ sc) = used n sc

    usedConst : String -> NamedConstAlt -> Bool
    usedConst n (MkNConstAlt _ sc) = used n sc

export
extractedMethodArgumentName : String
extractedMethodArgumentName = "$jvm$arg"

mutual
    liftToLambda : (isTailPosition: Bool) -> NamedCExp -> NamedCExp
    liftToLambda False (NmLet fc var value sc) = NmApp fc (NmLam fc var sc) [value]
    liftToLambda True (NmLet fc var value sc) = NmLet fc var (liftToLambda False value) (liftToLambda True sc)
    liftToLambda _ expr@(NmConCase _ sc [] Nothing) = expr
    liftToLambda False (NmConCase fc sc alts def) =
        let var = UN extractedMethodArgumentName
            liftedAlts = liftToLambdaCon <$> alts
            liftedDef = liftToLambdaDefault <$> def
        in NmApp fc (NmLam fc var (NmConCase fc (NmLocal fc var) liftedAlts liftedDef)) [liftToLambda False sc]
    liftToLambda True (NmConCase fc sc alts def) =
        NmConCase fc (liftToLambda False sc) (liftToLambdaCon <$> alts) (liftToLambdaDefault <$> def)
    liftToLambda _ expr@(NmConstCase fc sc [] Nothing) = expr
    liftToLambda False (NmConstCase fc sc alts def) =
        let var = UN extractedMethodArgumentName
            liftedAlts = liftToLambdaConst <$> alts
            liftedDef = liftToLambdaDefault <$> def
        in NmApp fc (NmLam fc var $ NmConstCase fc (NmLocal fc var) liftedAlts liftedDef) [liftToLambda False sc]
    liftToLambda True (NmConstCase fc sc alts def) =
        NmConstCase fc (liftToLambda False sc) (liftToLambdaConst <$> alts) (liftToLambdaDefault <$> def)
    liftToLambda _ (NmLam fc param sc) = NmLam fc param $ liftToLambda True sc
    liftToLambda _ (NmApp fc f args) = NmApp fc (liftToLambda False f) (liftToLambda False <$> args)
    liftToLambda _ expr@(NmCon fc name tag args) = NmCon fc name tag $ (liftToLambda False <$> args)
    liftToLambda _ (NmOp fc f args) = NmOp fc f (liftToLambda False <$> args)
    liftToLambda _ (NmExtPrim fc f args) = NmExtPrim fc f (liftToLambda False <$> args)
    liftToLambda _ (NmForce fc t) = NmForce fc $ liftToLambda False t
    liftToLambda _ (NmDelay fc t) = NmDelay fc $ liftToLambda False t
    liftToLambda _ expr = expr

    liftToLambdaDefault : NamedCExp -> NamedCExp
    liftToLambdaDefault body = liftToLambda True body

    liftToLambdaCon : NamedConAlt -> NamedConAlt
    liftToLambdaCon (MkNConAlt n tag args body) = MkNConAlt n tag args $ liftToLambda True body

    liftToLambdaConst : NamedConstAlt -> NamedConstAlt
    liftToLambdaConst (MkNConstAlt constant body) = MkNConstAlt constant (liftToLambda True body)

mutual
    goHasSingleUsage : Int -> Name -> NamedCExp -> Int
    goHasSingleUsage count name expr =
        if count > 1 then count
        else go expr
      where
        go : NamedCExp -> Int
        go (NmLocal fc var) = if name == var then count + 1 else count
        go (NmLam _ _ sc) = goHasSingleUsage count name sc
        go (NmLet _ var value sc) =
            let usageCountInValue = goHasSingleUsage count name value
            in goHasSingleUsage usageCountInValue name sc
        go (NmApp _ (NmRef _ _) args) = goHasSingleUsageExpressions count name args
        go (NmApp _ f args) =
            let lambdaExprUsageCount = goHasSingleUsage count name f
            in goHasSingleUsageExpressions lambdaExprUsageCount name args
        go (NmCon _ _ _ args) = goHasSingleUsageExpressions count name args
        go (NmOp _ _ args) = goHasSingleUsageExpressions count name $ toList args
        go (NmExtPrim _ _ args) = goHasSingleUsageExpressions count name args
        go (NmForce _ t) = goHasSingleUsage count name t
        go (NmDelay _ t) = goHasSingleUsage count name t
        go (NmConCase _ sc alts def) =
            let altsCount = goHasSingleUsageCon (goHasSingleUsage count name sc) name alts
            in maybe altsCount (goHasSingleUsage altsCount name) def
        go (NmConstCase _ sc alts def) =
            let altsCount = goHasSingleUsageConst (goHasSingleUsage count name sc) name alts
            in maybe altsCount (goHasSingleUsage altsCount name) def
        go _ = count

    goHasSingleUsageExpressions : Int -> Name -> List NamedCExp -> Int
    goHasSingleUsageExpressions count name expressions =
        if count > 1 then count
        else case expressions of
            [] => count
            (expr :: rest) => goHasSingleUsageExpressions (goHasSingleUsage count name expr) name rest

    goHasSingleUsageCon : Int -> Name -> List NamedConAlt -> Int
    goHasSingleUsageCon count name alts =
        if count > 1 then count
        else case alts of
            [] => count
            ((MkNConAlt _ _ _ sc) :: rest) => goHasSingleUsageCon (goHasSingleUsage count name sc) name rest

    goHasSingleUsageConst : Int -> Name -> List NamedConstAlt -> Int
    goHasSingleUsageConst count name alts =
        if count > 1 then count
        else case alts of
            [] => count
            ((MkNConstAlt _ sc) :: rest) => goHasSingleUsageConst (goHasSingleUsage count name sc) name rest

hasSingleUsage : Name -> NamedCExp -> Bool
hasSingleUsage name expr = goHasSingleUsage 0 name expr == 1

mutual
    doGetFreeVariables : SortedSet String -> SortedSet String -> NamedCExp -> SortedSet String
    doGetFreeVariables freeVariables boundVariables (NmLocal fc var) =
        let varName = jvmSimpleName var
        in
            if SortedSet.contains varName boundVariables then freeVariables
            else SortedSet.insert varName freeVariables
    doGetFreeVariables freeVariables boundVariables (NmLam _ parameterName body) =
        doGetFreeVariables freeVariables (SortedSet.insert (jvmSimpleName parameterName) boundVariables) body
    doGetFreeVariables freeVariables boundVariables (NmLet _ var value body) =
        let newFreeVariables = doGetFreeVariables freeVariables boundVariables value
            newBoundVariables = SortedSet.insert (jvmSimpleName var) boundVariables
        in doGetFreeVariables newFreeVariables newBoundVariables body
    doGetFreeVariables freeVariables boundVariables (NmApp _ (NmRef _ _) args) =
        getExpressionsFreeVariables freeVariables boundVariables args
    doGetFreeVariables freeVariables boundVariables (NmApp _ f args) =
        getExpressionsFreeVariables freeVariables boundVariables (f :: args)
    doGetFreeVariables freeVariables boundVariables (NmCon _ _ _ args) =
        getExpressionsFreeVariables freeVariables boundVariables args
    doGetFreeVariables freeVariables boundVariables (NmOp _ _ args) =
        getExpressionsFreeVariables freeVariables boundVariables $ toList args
    doGetFreeVariables freeVariables boundVariables (NmExtPrim _ _ args) =
        getExpressionsFreeVariables freeVariables boundVariables args
    doGetFreeVariables freeVariables boundVariables (NmForce _ t) =
        doGetFreeVariables freeVariables boundVariables t
    doGetFreeVariables freeVariables boundVariables (NmDelay _ t) =
        doGetFreeVariables freeVariables boundVariables t
    doGetFreeVariables freeVariables boundVariables (NmConCase _ sc alts def) =
        let switchExprFreeVariables = doGetFreeVariables freeVariables boundVariables sc
            altsFreeVariables = doGetFreeVariablesCon switchExprFreeVariables boundVariables alts
        in maybe altsFreeVariables (doGetFreeVariables altsFreeVariables boundVariables) def
    doGetFreeVariables freeVariables boundVariables (NmConstCase _ sc alts def) =
        let switchExprFreeVariables = doGetFreeVariables freeVariables boundVariables sc
            altsFreeVariables = doGetFreeVariablesConst switchExprFreeVariables boundVariables alts
        in maybe altsFreeVariables (doGetFreeVariables altsFreeVariables boundVariables) def
    doGetFreeVariables freeVariables _ _ = freeVariables

    getExpressionsFreeVariables : SortedSet String -> SortedSet String -> List NamedCExp -> SortedSet String
    getExpressionsFreeVariables freeVariables boundVariables expressions = go freeVariables expressions where
        go : SortedSet String -> List NamedCExp -> SortedSet String
        go freeVariables [] = freeVariables
        go freeVariables (arg :: args) = go (doGetFreeVariables freeVariables boundVariables arg) args

    doGetFreeVariablesCon : SortedSet String -> SortedSet String -> List NamedConAlt -> SortedSet String
    doGetFreeVariablesCon freeVariables _ [] = freeVariables
    doGetFreeVariablesCon freeVariables boundVariables ((MkNConAlt _ _ properties sc) :: rest) =
        let newBoundVariables = SortedSet.union boundVariables (SortedSet.fromList (jvmSimpleName <$> properties))
        in doGetFreeVariablesCon (doGetFreeVariables freeVariables newBoundVariables sc) boundVariables rest

    doGetFreeVariablesConst : SortedSet String -> SortedSet String -> List NamedConstAlt -> SortedSet String
    doGetFreeVariablesConst freeVariables _ [] = freeVariables
    doGetFreeVariablesConst freeVariables boundVariables ((MkNConstAlt _ sc) :: rest) =
        doGetFreeVariablesConst (doGetFreeVariables freeVariables boundVariables sc) boundVariables rest

getFreeVariables : SortedSet String -> NamedCExp -> SortedSet String
getFreeVariables boundVariables expr = doGetFreeVariables SortedSet.empty SortedSet.empty expr

mutual
    markTailRecursion : NamedCExp -> Asm NamedCExp
    markTailRecursion expr@(NmApp fc (NmRef nameFc idrisName) args) =
        maybe (Pure expr)
            (\functionName => if functionName == !getRootMethodName
                then Pure (NmApp fc (NmRef nameFc (UN ":__jvmTailRec__:")) args)
                else Pure expr)
            !(findJvmMethodNameForIdrisName (jvmName idrisName))
    markTailRecursion expr@(NmLet fc var value body) =
        NmLet fc var value <$> markTailRecursion body
    markTailRecursion expr@(NmConCase fc sc alts def) = do
        tailRecursionMarkedAlts <- traverse markTailRecursionConAlt alts
        tailRecursionMarkedDefault <- traverse markTailRecursion def
        Pure (NmConCase fc sc tailRecursionMarkedAlts tailRecursionMarkedDefault)
    markTailRecursion (NmConstCase fc sc alts def) = do
        tailRecursionMarkedAlts <- traverse markTailRecursionConstAlt alts
        tailRecursionMarkedDefault <- traverse markTailRecursion def
        Pure (NmConstCase fc sc tailRecursionMarkedAlts tailRecursionMarkedDefault)
    markTailRecursion expr = Pure expr

    markTailRecursionConAlt : NamedConAlt -> Asm NamedConAlt
    markTailRecursionConAlt (MkNConAlt name tag args caseBody) =
        MkNConAlt name tag args <$> markTailRecursion caseBody

    markTailRecursionConstAlt : NamedConstAlt -> Asm NamedConstAlt
    markTailRecursionConstAlt (MkNConstAlt constant caseBody) = MkNConstAlt constant <$> markTailRecursion caseBody

mutual
    trampolineExpression : NamedCExp -> Asm NamedCExp
    trampolineExpression expr@(NmApp fc (NmRef nameFc (UN ":__jvmTailRec__:")) args) =
        -- Do not trampoline as tail recursion will be eliminated
        Pure expr
    trampolineExpression expr@(NmCon _ _ _ _) = Pure $ thunkExpr expr
    trampolineExpression expr@(NmApp _ _ _) = Pure $ thunkExpr expr
    trampolineExpression expr@(NmLet fc var value body) =
        NmLet fc var value <$> trampolineExpression body
    trampolineExpression expr@(NmConCase fc sc alts def) = do
        trampolinedAlts <- traverse trampolineExpressionConAlt alts
        trampolinedDefault <- traverse trampolineExpression def
        Pure (NmConCase fc sc trampolinedAlts trampolinedDefault)
    trampolineExpression (NmConstCase fc sc alts def) = do
        trampolinedAlts <- traverse trampolineExpressionConstAlt alts
        trampolinedDefault <- traverse trampolineExpression def
        Pure (NmConstCase fc sc trampolinedAlts trampolinedDefault)
    trampolineExpression expr = Pure expr

    trampolineExpressionConAlt : NamedConAlt -> Asm NamedConAlt
    trampolineExpressionConAlt (MkNConAlt name tag args caseBody) = 
        MkNConAlt name tag args <$> trampolineExpression caseBody

    trampolineExpressionConstAlt : NamedConstAlt -> Asm NamedConstAlt
    trampolineExpressionConstAlt (MkNConstAlt constant caseBody) =
        MkNConstAlt constant <$> trampolineExpression caseBody

mutual            
    inlineVariable : Name -> NamedCExp -> NamedCExp -> NamedCExp
    inlineVariable var value expr@(NmLocal fc loc) = if loc == var then value else expr
    inlineVariable var value expr@(NmRef _ _) = expr
    inlineVariable var value (NmLam fc param sc) = NmLam fc param $ inlineVariable var value sc
    inlineVariable var value (NmLet fc letVar letValue letBody) =
        NmLet fc letVar (inlineVariable var value letValue) (inlineVariable var value letBody)
    inlineVariable var value (NmApp fc f@(NmRef _ _) args) =
        NmApp fc f (inlineVariable var value <$> args)
    inlineVariable var value (NmApp fc f args) =
        NmApp fc (inlineVariable var value f) (inlineVariable var value <$> args)
    inlineVariable var value (NmCon fc name tag args) =
        NmCon fc name tag $ (inlineVariable var value <$> args)
    inlineVariable var value (NmOp fc op args) = NmOp fc op (inlineVariable var value <$> args)
    inlineVariable var value (NmExtPrim fc name args) = NmExtPrim fc name (inlineVariable var value <$> args)
    inlineVariable var value (NmForce fc t) = NmForce fc $ inlineVariable var value t
    inlineVariable var value (NmDelay fc t) = NmDelay fc $ inlineVariable var value t
    inlineVariable var value (NmConCase fc sc alts def)
        = NmConCase fc (inlineVariable var value sc) (inlineVariableCon var value <$> alts)
              (inlineVariable var value <$> def)
    inlineVariable var value (NmConstCase fc sc alts def)
        = NmConstCase fc (inlineVariable var value sc) (inlineVariableConst var value <$> alts)
              (inlineVariable var value <$> def)
    inlineVariable _ _ expr = expr

    inlineVariableCon : Name -> NamedCExp -> NamedConAlt -> NamedConAlt
    inlineVariableCon var value (MkNConAlt name tag args sc) = MkNConAlt name tag args $ inlineVariable var value sc

    inlineVariableConst : Name -> NamedCExp -> NamedConstAlt -> NamedConstAlt
    inlineVariableConst var value (MkNConstAlt constant sc) = MkNConstAlt constant $ inlineVariable var value sc

mutual
    eliminateSingleUsageVariable : NamedCExp -> NamedCExp
    eliminateSingleUsageVariable (NmLet fc var value body) = 
        if hasSingleUsage var body then
            eliminateSingleUsageVariable $ inlineVariable var value body
        else NmLet fc var (eliminateSingleUsageVariable value) (eliminateSingleUsageVariable body)
    eliminateSingleUsageVariable (NmLam fc param body) = NmLam fc param $ eliminateSingleUsageVariable body
    eliminateSingleUsageVariable (NmApp fc f args) =
        NmApp fc f (eliminateSingleUsageVariable <$> args)
    eliminateSingleUsageVariable (NmCon fc name tag args) =
        NmCon fc name tag $ (eliminateSingleUsageVariable <$> args)
    eliminateSingleUsageVariable (NmOp fc op args) = NmOp fc op (eliminateSingleUsageVariable <$> args)
    eliminateSingleUsageVariable (NmExtPrim fc name args) = NmExtPrim fc name (eliminateSingleUsageVariable <$> args)
    eliminateSingleUsageVariable (NmForce fc t) = NmForce fc $ eliminateSingleUsageVariable t
    eliminateSingleUsageVariable (NmDelay fc t) = NmDelay fc $ eliminateSingleUsageVariable t
    eliminateSingleUsageVariable (NmConCase fc sc alts def)
        = NmConCase fc (eliminateSingleUsageVariable sc) (eliminateSingleUsageVariableCon <$> alts)
              (eliminateSingleUsageVariable <$> def)
    eliminateSingleUsageVariable (NmConstCase fc sc alts def)
        = NmConstCase fc (eliminateSingleUsageVariable sc) (eliminateSingleUsageVariableConst <$> alts)
              (eliminateSingleUsageVariable <$> def)
    eliminateSingleUsageVariable expr = expr
    
    eliminateSingleUsageVariableCon : NamedConAlt -> NamedConAlt
    eliminateSingleUsageVariableCon (MkNConAlt name tag args sc) =
        MkNConAlt name tag args $ eliminateSingleUsageVariable sc

    eliminateSingleUsageVariableConst : NamedConstAlt -> NamedConstAlt
    eliminateSingleUsageVariableConst (MkNConstAlt constant sc) = MkNConstAlt constant $ eliminateSingleUsageVariable sc

exitInferenceScope : Int -> Asm ()
exitInferenceScope scopeIndex = updateCurrentScopeIndex scopeIndex

enterInferenceScope : Int -> Int -> Asm ()
enterInferenceScope lineNumberStart lineNumberEnd = do
    parentScopeIndex <- getCurrentScopeIndex
    scopeIndex <- newScopeIndex
    parentScope <- getScope parentScopeIndex
    let newScope = MkScope scopeIndex (Just parentScopeIndex) SortedMap.empty SortedMap.empty SortedMap.empty
        SortedMap.empty IUnknown (nextVariableIndex parentScope) (lineNumberStart, lineNumberEnd) ("", "") []
    addScopeChild parentScopeIndex scopeIndex
    saveScope newScope
    updateCurrentScopeIndex scopeIndex

createLambdaClosureScope : Int -> Int -> List String -> Scope -> Asm Scope
createLambdaClosureScope scopeIndex childScopeIndex closureVariables parentScope = do
        let lambdaClosureVariableIndices = SortedMap.fromList $ getLambdaClosureVariableIndices [] 0 closureVariables
        Pure $ MkScope scopeIndex (Just $ index parentScope) SortedMap.empty SortedMap.empty
            lambdaClosureVariableIndices SortedMap.empty IUnknown (cast $ length closureVariables) (lineNumbers parentScope)
            ("", "") [childScopeIndex]
    where
        getLambdaClosureVariableIndices : List (String, Int) -> Int -> List String -> List (String, Int)
        getLambdaClosureVariableIndices acc _ [] = acc
        getLambdaClosureVariableIndices acc index (var :: vars) = 
            getLambdaClosureVariableIndices ((var, index) :: acc) (index + 1) vars

enterInferenceLambdaScope : Int -> Int -> Maybe Name -> NamedCExp -> Asm ()
enterInferenceLambdaScope lineNumberStart lineNumberEnd parameterName expr = do
        parentScopeIndex <- getCurrentScopeIndex
        scopeIndex <- newScopeIndex
        let boundVariables = maybe SortedSet.empty (flip SortedSet.insert SortedSet.empty . jvmSimpleName) parameterName
        let freeVariables = getFreeVariables boundVariables expr
        let usedVariables = filter (flip SortedSet.contains freeVariables) !(retrieveVariables parentScopeIndex)
        newScope <- case usedVariables  of
            nonEmptyUsedVariables@(_ :: _) => do
                parentScope <- getScope parentScopeIndex
                lambdaParentScopeIndex <- newScopeIndex
                closureScope <- createLambdaClosureScope lambdaParentScopeIndex scopeIndex nonEmptyUsedVariables
                    parentScope
                saveScope closureScope
                let closureVariableCount = nextVariableIndex closureScope
                Pure $ MkScope scopeIndex (Just lambdaParentScopeIndex) SortedMap.empty SortedMap.empty
                    SortedMap.empty SortedMap.empty IUnknown closureVariableCount (lineNumberStart, lineNumberEnd)
                    ("", "") []
            [] => Pure $ MkScope scopeIndex Nothing SortedMap.empty SortedMap.empty SortedMap.empty SortedMap.empty
                IUnknown 0 (lineNumberStart, lineNumberEnd) ("", "") []
        saveScope newScope
        updateCurrentScopeIndex scopeIndex

withInferenceScope : Int -> Int -> Asm result -> Asm result
withInferenceScope lineNumberStart lineNumberEnd op = do
    scopeIndex <- getCurrentScopeIndex
    enterInferenceScope lineNumberStart lineNumberEnd
    result <- op
    exitInferenceScope scopeIndex
    Pure result

withInferenceLambdaScope : Int -> Int -> Maybe Name -> NamedCExp -> Asm result -> Asm result
withInferenceLambdaScope lineNumberStart lineNumberEnd parameterName expr op = do
    scopeIndex <- getCurrentScopeIndex
    enterInferenceLambdaScope lineNumberStart lineNumberEnd parameterName expr
    result <- op
    exitInferenceScope scopeIndex
    Pure result

public export
data LambdaType = ThunkLambda | DelayedLambda | FunctionLambda

export
Eq LambdaType where
    ThunkLambda == ThunkLambda = True
    DelayedLambda == DelayedLambda = True
    FunctionLambda == FunctionLambda = True
    _ == _ = False

export
getLambdaType : (parameterName: Maybe Name) -> LambdaType
getLambdaType (Just (UN "$jvm$thunk")) = ThunkLambda
getLambdaType Nothing = DelayedLambda
getLambdaType _ = FunctionLambda

export
getLambdaInterfaceMethodName : LambdaType -> String
getLambdaInterfaceMethodName FunctionLambda = "apply"
getLambdaInterfaceMethodName _ = "evaluate"

export
getSamDesc : LambdaType -> String
getSamDesc ThunkLambda = "()" ++ getJvmTypeDescriptor thunkType
getSamDesc DelayedLambda = "()Ljava/lang/Object;"
getSamDesc FunctionLambda = "(Ljava/lang/Object;)Ljava/lang/Object;"

export
getLambdaInterfaceType : LambdaType -> InferredType -> InferredType
getLambdaInterfaceType ThunkLambda returnType = getThunkType returnType
getLambdaInterfaceType DelayedLambda returnType = delayedType
getLambdaInterfaceType FunctionLambda returnType = inferredLambdaType

export
getLambdaImplementationMethodReturnType : LambdaType -> InferredType
getLambdaImplementationMethodReturnType ThunkLambda = thunkType
getLambdaImplementationMethodReturnType _ = inferredObjectType

export
getConstantType : List NamedConstAlt -> Asm InferredType
getConstantType [] = Throw emptyFC "Unknown constant switch type"
getConstantType ((MkNConstAlt constant _) :: _) = case constant of
    I _ => Pure IInt
    Ch _ => Pure IInt
    Str _ => Pure inferredStringType
    BI _ => Pure inferredBigIntegerType
    unsupportedConstant => Throw emptyFC $ "Unsupported constant switch " ++ show unsupportedConstant

export
isTypeConst : TT.Constant -> Bool
isTypeConst IntType     = True
isTypeConst IntegerType = True
isTypeConst StringType  = True
isTypeConst CharType    = True
isTypeConst DoubleType  = True
isTypeConst WorldType   = True
isTypeConst _           = False

export
getIntConstantValue : FC -> TT.Constant -> Asm Int
getIntConstantValue _ (I i) = Pure i
getIntConstantValue _ (Ch c) = Pure $ ord c
getIntConstantValue _ WorldVal = Pure 0
getIntConstantValue fc x =
    if isTypeConst x then Pure 0
    else Throw fc ("Constant " ++ show x ++ " cannot be converted to integer.")

sortConCases : List NamedConAlt -> List NamedConAlt
sortConCases alts = sortBy (comparing getTag) alts where
    getTag : NamedConAlt -> Int
    getTag (MkNConAlt _ tag _ _) = fromMaybe 0 tag

export
isTypeCase : NamedConAlt -> Bool
isTypeCase (MkNConAlt _ Nothing _ _) = True
isTypeCase _ = False

export
substituteVariableSubMethodBody : NamedCExp -> NamedCExp -> NamedCExp
substituteVariableSubMethodBody variable (NmConCase fc _ alts def) = NmConCase fc variable alts def
substituteVariableSubMethodBody variable (NmConstCase fc _ alts def) = NmConstCase fc variable alts def
substituteVariableSubMethodBody _ expr = expr

combineSwitchTypes : Maybe InferredType -> List InferredType -> InferredType
combineSwitchTypes defaultTy [] = fromMaybe IUnknown defaultTy
combineSwitchTypes defaultTy altTypes@(altTy :: rest) = maybe (go altTy rest) (flip go altTypes) defaultTy where
  go : InferredType -> List InferredType -> InferredType
  go prevTy [] = prevTy
  go prevTy (currTy :: rest) = if prevTy == currTy then go currTy rest else inferredObjectType

mutual
    inferExpr : InferredType -> NamedCExp -> Asm InferredType
    inferExpr exprTy (NmDelay _ expr) = inferExprLam Nothing Nothing expr
    inferExpr exprTy expr@(NmLocal _ var) = addVariableType (jvmSimpleName var) exprTy
    inferExpr exprTy (NmRef _ _) = pure exprTy
    inferExpr _ (NmApp _ (NmLam _ var body) [expr]) = inferExprLam (Just expr) (Just var) body
    inferExpr _ (NmLam _ var body) = inferExprLam Nothing (Just var) body
    inferExpr exprTy (NmLet fc var value expr) = inferExprLet fc exprTy var value expr
    inferExpr exprTy app@(NmApp _ _ _) = inferExprApp exprTy app
    inferExpr exprTy expr@(NmCon fc name tag args) =
        inferExprCon exprTy (fst $ getSourceLocation expr) name args
    inferExpr exprTy (NmOp _ fn args) = inferExprOp fn args
    inferExpr exprTy (NmExtPrim fc fn args) = inferExtPrim fc exprTy (toPrim fn) args
    inferExpr exprTy (NmForce _ expr) = inferExpr delayedType expr

    inferExpr exprTy (NmConCase _ sc [] Nothing) = Pure IUnknown
    inferExpr exprTy (NmConCase _ sc [] (Just def)) = do
        inferConstructorSwitchExpr sc
        inferExpr exprTy def
    inferExpr exprTy (NmConCase _ sc [MkNConAlt _ _ args expr] Nothing) = do
        inferConstructorSwitchExpr sc
        inferConCaseExpr exprTy args expr
    inferExpr exprTy (NmConCase _ sc alts def) = do
        inferConstructorSwitchExpr sc
        let hasTypeCase = any isTypeCase alts
        when hasTypeCase $ do
            constantExprVariable <- generateVariable "constructorCaseExpr"
            addVariableType constantExprVariable inferredStringType
            hashCodePositionVariable <- generateVariable "hashCodePosition"
            addVariableType hashCodePositionVariable IInt
            Pure ()
        let sortedAlts = if hasTypeCase then alts else sortConCases alts
        altTypes <- traverse (inferExprConAlt exprTy) sortedAlts
        defaultTy <- traverse (inferExprWithNewScope exprTy) def
        Pure $ combineSwitchTypes defaultTy altTypes

    inferExpr exprTy (NmConstCase fc sc [] Nothing) = Pure IUnknown
    inferExpr exprTy (NmConstCase fc sc [] (Just expr)) = inferExpr exprTy expr
    inferExpr exprTy (NmConstCase fc sc alts def) = do
        constantType <- getConstantType alts
        inferExpr constantType sc
        when (constantType /= IInt) $ do
            constantExprVariable <- generateVariable "constantCaseExpr"
            addVariableType constantExprVariable constantType
            hashCodePositionVariable <- generateVariable "hashCodePosition"
            addVariableType hashCodePositionVariable IInt
            Pure ()
        sortedAlts <- sortConstCases constantType alts
        altTypes <- traverse (inferExprConstAlt exprTy) sortedAlts
        defaultTy <- traverse (inferExprWithNewScope exprTy) def
        Pure $ combineSwitchTypes defaultTy altTypes
      where
        getConstant : NamedConstAlt -> TT.Constant
        getConstant (MkNConstAlt constant _) = constant

        sortConstCases : InferredType -> List NamedConstAlt -> Asm (List NamedConstAlt)
        sortConstCases IInt alts = do
            constValues <- traverse (getIntConstantValue fc . getConstant) alts
            Pure $ fst <$> (sortBy (comparing snd) $ List.zip alts constValues)
        sortConstCases _ alts = Pure alts

    inferExpr _ (NmPrimVal fc (I _)) = pure IInt
    inferExpr _ (NmPrimVal fc (BI _)) = pure inferredBigIntegerType
    inferExpr _ (NmPrimVal fc (Str _)) = pure inferredStringType
    inferExpr _ (NmPrimVal fc (Ch _)) = pure IChar
    inferExpr _ (NmPrimVal fc (Db _)) = pure IDouble
    inferExpr _ (NmPrimVal fc WorldVal) = pure inferredObjectType
    inferExpr exprTy (NmErased fc) = pure exprTy
    inferExpr exprTy (NmCrash fc msg) = pure exprTy
    inferExpr exprTy expr = Throw (getFC expr) ("Unsupported expr " ++ show expr)

    inferConstructorSwitchExpr : NamedCExp -> Asm ()
    inferConstructorSwitchExpr sc = do
        idrisObjectVariable <- case sc of
            (NmLocal _ var) => Pure $ jvmSimpleName var
            _ => generateVariable "constructorSwitchValue"
        inferExpr idrisObjectType sc
        addVariableType idrisObjectVariable idrisObjectType
        Pure ()

    inferExprConstAlt : InferredType -> NamedConstAlt -> Asm InferredType
    inferExprConstAlt returnType (MkNConstAlt _ expr) = inferExprWithNewScope returnType expr

    inferExprWithNewScope : InferredType -> NamedCExp -> Asm InferredType
    inferExprWithNewScope returnType expr = do
         let fc = getFC expr
         let (lineStart, lineEnd) = getLineNumbers (startPos fc) (endPos fc)
         withInferenceScope lineStart lineEnd $ inferExpr returnType expr

    inferConCaseExpr : InferredType -> List Name -> NamedCExp -> Asm InferredType
    inferConCaseExpr exprTy args expr = do
            traverse_ inferArg args
            inferExpr exprTy expr
        where
            inferArg : Name -> Asm ()
            inferArg var =
                let variableName = jvmSimpleName var
                in when (used variableName expr) $ createVariable variableName

    inferExprConAlt : InferredType -> NamedConAlt -> Asm InferredType
    inferExprConAlt exprTy (MkNConAlt _ _ args expr) = do
            let fc = getFC expr
            let (lineStart, lineEnd) = getLineNumbers (startPos fc) (endPos fc)
            withInferenceScope lineStart lineEnd $ inferConCaseExpr exprTy args expr

    inferParameter : (NamedCExp, InferredType) -> Asm InferredType
    inferParameter (param, ty) = inferExpr ty param

    inferBinaryOp : InferredType -> NamedCExp -> NamedCExp -> Asm InferredType
    inferBinaryOp ty x y = do
        inferExpr ty x
        inferExpr ty y
        pure ty

    inferBoolOp : InferredType -> NamedCExp -> NamedCExp -> Asm InferredType
    inferBoolOp ty x y = do
        inferExpr ty x
        inferExpr ty y
        pure IBool

    inferUnaryOp : InferredType -> NamedCExp -> Asm InferredType
    inferUnaryOp ty x = do inferExpr ty x; Pure ty

    inferExtPrimArg : (NamedCExp, InferredType) -> Asm InferredType
    inferExtPrimArg (arg, ty) = inferExpr ty arg

    inferExtPrim : FC -> InferredType -> ExtPrim -> List NamedCExp -> Asm InferredType
    inferExtPrim fc returnType JvmInstanceMethodCall descriptors =
        inferExtPrim fc returnType JvmStaticMethodCall descriptors
    inferExtPrim _ returnType JvmStaticMethodCall [ret, NmPrimVal fc (Str fn), fargs, world]
      = do args <- getFArgs fargs
           argTypes <- traverse tySpec (map fst args)
           methodReturnType <- tySpec ret
           traverse inferExtPrimArg $ List.zip (map snd args) argTypes
           let (cname, mnameWithDot) = break (== '.') fn
           let (_, mname) = break (/= '.') mnameWithDot
           pure methodReturnType
    inferExtPrim _ returnType NewArray [_, size, val, world] = do
        inferExpr IInt size
        inferExpr IUnknown val
        pure arrayListType
    inferExtPrim _ returnType ArrayGet [_, arr, pos, world] = do
        inferExpr arrayListType arr
        inferExpr IInt pos
        pure IUnknown
    inferExtPrim _ returnType ArraySet [_, arr, pos, val, world] = do
        inferExpr arrayListType arr
        inferExpr IInt pos
        inferExpr IUnknown val
        pure inferredObjectType
    inferExtPrim _ returnType NewIORef [_, val, world] = do
        inferExpr IUnknown val
        pure refType
    inferExtPrim _ returnType ReadIORef [_, ref, world] = do
        inferExpr refType ref
        pure IUnknown
    inferExtPrim _ returnType WriteIORef [_, ref, val, world] = do
        inferExpr refType ref
        inferExpr IUnknown val
        pure inferredObjectType
    inferExtPrim _ returnType SysOS [] = pure inferredStringType
    inferExtPrim _ returnType SysCodegen [] = pure inferredStringType
    inferExtPrim fc _ prim args = Throw fc $ "Unsupported external function " ++ show prim ++ "(" ++
        (show $ showNamedCExp 0 <$> args) ++ ")"

    inferExprLamWithParameterType : Maybe (Name, InferredType) -> (parameterValueExpr: Maybe (Asm ())) ->
        NamedCExp -> Asm InferredType
    inferExprLamWithParameterType parameterNameAndType parameterValueExpr expr = do
        let hasParameterValue = isJust parameterValueExpr
        let (_, lineStart, lineEnd) = getSourceLocation expr
        let jvmParameterNameAndType = (\(name, ty) => (jvmSimpleName name, ty)) <$> parameterNameAndType
        let lambdaType = getLambdaType (fst <$> parameterNameAndType)
        lambdaBodyReturnType <- withInferenceLambdaScope lineStart lineEnd (fst <$> parameterNameAndType) expr $ do
            when (lambdaType /= ThunkLambda) $
                traverse_ createAndAddVariable jvmParameterNameAndType
            maybe (Pure ()) id parameterValueExpr
            lambdaBodyReturnType <- inferExpr IUnknown expr
            currentScope <- getScope !getCurrentScopeIndex
            saveScope $ record {returnType = lambdaBodyReturnType} currentScope
            Pure lambdaBodyReturnType
        Pure $ if hasParameterValue then lambdaBodyReturnType
            else getLambdaInterfaceType lambdaType lambdaBodyReturnType
      where
        createAndAddVariable : (String, InferredType) -> Asm ()
        createAndAddVariable (name, ty) = do
            createVariable name
            addVariableType name ty
            Pure ()

    inferExprLam : (parameterValue: Maybe NamedCExp) -> (parameterName : Maybe Name) -> NamedCExp -> Asm InferredType
    inferExprLam parameterValue@(Just value) (Just name) expr = do
        valueType <- case expr of
            (NmConstCase _ _ alts _) => getConstantType alts
            (NmConCase _ _ _ _) => Pure idrisObjectType
            _ => Pure IUnknown
        let shouldGenerateVariable = name == UN extractedMethodArgumentName
        let generatedJvmVariableName =
            if shouldGenerateVariable then jvmSimpleName name ++ show !newDynamicVariableIndex
            else jvmSimpleName name
        let generatedVariableName =
            if shouldGenerateVariable then UN generatedJvmVariableName
            else name
        let valueExpr = NmLocal (getFC expr) generatedVariableName
        parentScope <- getScope !getCurrentScopeIndex
        inferExprLamWithParameterType (Just (generatedVariableName, valueType))
            (Just (inferValue parentScope shouldGenerateVariable generatedJvmVariableName valueType))
            (substituteVariableSubMethodBody valueExpr expr)
      where
        inferValue : Scope -> Bool -> String -> InferredType -> Asm ()
        inferValue enclosingScope shouldGenerateVariable variableName valueType = do
            lambdaScopeIndex <- getCurrentScopeIndex
            updateCurrentScopeIndex (index enclosingScope)
            inferExpr valueType value
            when shouldGenerateVariable $ createVariable variableName
            addVariableType variableName valueType
            updateCurrentScopeIndex lambdaScopeIndex
    inferExprLam _ parameterName expr =
        inferExprLamWithParameterType ((\name => (name, inferredObjectType)) <$> parameterName) Nothing expr

    inferExprLet : FC -> InferredType -> (x : Name) -> NamedCExp -> NamedCExp -> Asm InferredType
    inferExprLet fc exprTy var value expr = do
        let (lineStart, lineEnd) = getLineNumbers (startPos fc) (endPos fc)
        let varName = jvmSimpleName var
        createVariable varName
        let (_, lineStart, lineEnd) = getSourceLocation value
        valueTy <- withInferenceScope lineStart lineEnd $ inferExpr IUnknown value
        addVariableType varName (if isThunkType valueTy then inferredObjectType else valueTy)
        let (_, lineStart, lineEnd) = getSourceLocation expr
        withInferenceScope lineStart lineEnd $ inferExpr exprTy expr

    inferSelfTailCallParameter : SortedMap Int InferredType -> SortedMap Int String ->
        (NamedCExp, Int) -> Asm ()
    inferSelfTailCallParameter types argumentNameByIndices (arg, index) = do
        let variableType = fromMaybe IUnknown $ SortedMap.lookup index types
        ty <- inferExpr variableType arg
        maybe (Pure ()) (\name => do addVariableType name ty; Pure ()) $ SortedMap.lookup index argumentNameByIndices

    inferExprApp : InferredType -> NamedCExp -> Asm InferredType
    inferExprApp exprTy app@(NmApp _ (NmRef _ (UN ":__jvmTailRec__:")) args) =
        case args of
            [] => Pure exprTy
            args@(_ :: argsTail) => do
                types <- retrieveVariableTypesAtScope !getCurrentScopeIndex
                let argumentNameByIndices = SortedMap.fromList (map swap $ toList $ variableIndices !(getScope 0))
                traverse (inferSelfTailCallParameter types argumentNameByIndices) $
                    List.zip args [0 .. the Int $ cast $ length argsTail]
                Pure exprTy
    inferExprApp exprTy (NmApp _ (NmRef _ idrisName) args) = do
        let functionName = jvmName idrisName
        let functionType = fromMaybe (MkInferredFunctionType IUnknown $ replicate (length args) IUnknown)
            !(findFunctionType functionName)
        let argsWithTypes = List.zip args (parameterTypes functionType)
        traverse_ inferParameter argsWithTypes
        Pure $ returnType functionType
    inferExprApp exprTy (NmApp _ lambdaVariable args) = do
        inferExpr inferredLambdaType lambdaVariable
        let argsWithTypes = List.zip args (replicate (length args) IUnknown)
        traverse_ inferParameter argsWithTypes
        pure IUnknown

    inferExprCon : InferredType -> String -> Name -> List NamedCExp -> Asm InferredType
    inferExprCon exprTy fileName name args = do
        let argsWithTypes = List.zip args (replicate (length args) IUnknown)
        traverse_ inferParameter argsWithTypes
        pure idrisObjectType

    inferExprOp : PrimFn arity -> Vect arity NamedCExp -> Asm InferredType
    inferExprOp (Add IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (Sub IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (Mul IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (Div IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (Mod IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (Neg IntType) [x] = inferUnaryOp IInt x
    inferExprOp (ShiftL IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (ShiftR IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (BAnd IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (BOr IntType) [x, y] = inferBinaryOp IInt x y
    inferExprOp (BXOr IntType) [x, y] = inferBinaryOp IInt x y

    inferExprOp (Add IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (Sub IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (Mul IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (Div IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (Mod IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (Neg IntegerType) [x] = inferUnaryOp inferredBigIntegerType x
    inferExprOp (ShiftL IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (ShiftR IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (BAnd IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (BOr IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y
    inferExprOp (BXOr IntegerType) [x, y] = inferBinaryOp inferredBigIntegerType x y

    inferExprOp (Add DoubleType) [x, y] = inferBinaryOp IDouble x y
    inferExprOp (Sub DoubleType) [x, y] = inferBinaryOp IDouble x y
    inferExprOp (Mul DoubleType) [x, y] = inferBinaryOp IDouble x y
    inferExprOp (Div DoubleType) [x, y] = inferBinaryOp IDouble x y
    inferExprOp (Neg DoubleType) [x] = inferUnaryOp IDouble x

    inferExprOp (LT IntType) [x, y] = inferBoolOp IInt x y
    inferExprOp (LT CharType) [x, y] = inferBoolOp IChar x y
    inferExprOp (LT IntegerType) [x, y] = inferBoolOp inferredBigIntegerType x y
    inferExprOp (LT DoubleType) [x, y] = inferBoolOp IDouble x y
    inferExprOp (LT StringType) [x, y] = inferBoolOp inferredStringType x y
    inferExprOp (LTE IntType) [x, y] = inferBoolOp IInt x y
    inferExprOp (LTE CharType) [x, y] = inferBoolOp IChar x y
    inferExprOp (LTE IntegerType) [x, y] = inferBoolOp inferredBigIntegerType x y
    inferExprOp (LTE DoubleType) [x, y] = inferBoolOp IDouble x y
    inferExprOp (LTE StringType) [x, y] = inferBoolOp inferredStringType x y
    inferExprOp (EQ IntType) [x, y] = inferBoolOp IInt x y
    inferExprOp (EQ CharType) [x, y] = inferBoolOp IChar x y
    inferExprOp (EQ IntegerType) [x, y] = inferBoolOp inferredBigIntegerType x y
    inferExprOp (EQ DoubleType) [x, y] = inferBoolOp IDouble x y
    inferExprOp (EQ StringType) [x, y] = inferBoolOp inferredStringType x y
    inferExprOp (GT IntType) [x, y] = inferBoolOp IInt x y
    inferExprOp (GT CharType) [x, y] = inferBoolOp IChar x y
    inferExprOp (GT IntegerType) [x, y] = inferBoolOp inferredBigIntegerType x y
    inferExprOp (GT DoubleType) [x, y] = inferBoolOp IDouble x y
    inferExprOp (GT StringType) [x, y] = inferBoolOp inferredStringType x y
    inferExprOp (GTE IntType) [x, y] = inferBoolOp IInt x y
    inferExprOp (GTE CharType) [x, y] = inferBoolOp IChar x y
    inferExprOp (GTE IntegerType) [x, y] = inferBoolOp inferredBigIntegerType x y
    inferExprOp (GTE DoubleType) [x, y] = inferBoolOp IDouble x y
    inferExprOp (GTE StringType) [x, y] = inferBoolOp inferredStringType x y
    inferExprOp StrLength [x] = do
        inferExpr inferredStringType x
        pure IInt
    inferExprOp StrHead [x] = do
        inferExpr inferredStringType x
        pure IChar
    inferExprOp StrTail [x] = do
        inferExpr inferredStringType x
        pure inferredStringType
    inferExprOp StrIndex [x, i] = do
        inferExpr inferredStringType x
        inferExpr IInt i
        pure IChar
    inferExprOp StrCons [x, y] = do
        inferExpr IChar x
        inferExpr inferredStringType y
        pure inferredStringType
    inferExprOp StrAppend [x, y] = inferBinaryOp inferredStringType x y
    inferExprOp StrReverse [x] = do
        inferExpr inferredStringType x
        pure inferredStringType
    inferExprOp StrSubstr [offset, len, str] = do
        inferExpr IInt offset
        inferExpr IInt len
        inferExpr inferredStringType str
        pure inferredStringType
    inferExprOp DoubleExp [x] = inferUnaryOp IDouble x
    inferExprOp DoubleLog [x] = inferUnaryOp IDouble x
    inferExprOp DoubleSin [x] = inferUnaryOp IDouble x
    inferExprOp DoubleCos [x] = inferUnaryOp IDouble x
    inferExprOp DoubleTan [x] = inferUnaryOp IDouble x
    inferExprOp DoubleASin [x] = inferUnaryOp IDouble x
    inferExprOp DoubleACos [x] = inferUnaryOp IDouble x
    inferExprOp DoubleATan [x] = inferUnaryOp IDouble x
    inferExprOp DoubleSqrt [x] = inferUnaryOp IDouble x
    inferExprOp DoubleFloor [x] = inferUnaryOp IDouble x
    inferExprOp DoubleCeiling [x] = inferUnaryOp IDouble x

    inferExprOp (Cast IntType StringType) [x] = do
        inferExpr IInt x
        pure inferredStringType
    inferExprOp (Cast IntegerType StringType) [x] = do
        inferExpr inferredBigIntegerType x
        pure inferredStringType
    inferExprOp (Cast DoubleType StringType) [x] = do
        inferExpr IDouble x
        pure inferredStringType
    inferExprOp (Cast CharType StringType) [x] = do
        inferExpr IChar x
        pure inferredStringType

    inferExprOp (Cast IntType IntegerType) [x] = do
        inferExpr IInt x
        pure inferredBigIntegerType
    inferExprOp (Cast DoubleType IntegerType) [x] = do
        inferExpr IDouble x
        pure inferredBigIntegerType
    inferExprOp (Cast CharType IntegerType) [x] = do
        inferExpr IChar x
        pure inferredBigIntegerType
    inferExprOp (Cast StringType IntegerType) [x] = do
        inferExpr inferredStringType x
        pure inferredBigIntegerType

    inferExprOp (Cast IntegerType IntType) [x] = do
        inferExpr inferredBigIntegerType x
        pure IInt
    inferExprOp (Cast DoubleType IntType) [x] = do
        inferExpr IDouble x
        pure IInt
    inferExprOp (Cast StringType IntType) [x] = do
        inferExpr inferredStringType x
        pure IInt
    inferExprOp (Cast CharType IntType) [x] = do
        inferExpr IChar x
        pure IInt

    inferExprOp (Cast IntegerType DoubleType) [x] = do
        inferExpr inferredBigIntegerType x
        pure IDouble
    inferExprOp (Cast IntType DoubleType) [x] = do
        inferExpr IInt x
        pure IDouble
    inferExprOp (Cast StringType DoubleType) [x] = do
        inferExpr inferredStringType x
        pure IDouble

    inferExprOp (Cast IntType CharType) [x] = do
        inferExpr IInt x
        pure IChar

    inferExprOp BelieveMe [_, _, x] = Pure IUnknown
    inferExprOp Crash [_, msg] = Pure IUnknown
    inferExprOp op _ = Throw emptyFC ("Unsupported expr " ++ show op)

optimize : TailCallCategory -> NamedCExp -> Asm NamedCExp
optimize tailCallCategory expr = do
    inlinedAndTailRecursionMarkedExpr <- markTailRecursion . liftToLambda True $ eliminateSingleUsageVariable expr
    if hasNonSelfTailCall tailCallCategory then trampolineExpression inlinedAndTailRecursionMarkedExpr
    else Pure inlinedAndTailRecursionMarkedExpr

export
inferDef : Name -> FC -> NamedDef -> Asm ()
inferDef idrisName fc (MkNmFun args expr) = do
        let jname = jvmName idrisName
        let hasSelfTailCall = hasTailCall (== idrisName) expr
        let hasNonSelfTailCall = hasTailCall (/= idrisName) expr
        let fileName = fst $ getSourceLocationFromFc fc
        let jvmClassAndMethodName = getIdrisFunctionName (className jname) fileName (methodName jname)
        let tailCallCategory = MkTailCallCategory hasSelfTailCall hasNonSelfTailCall
        let arity = length args
        let arityInt = the Int $ cast arity
        let argumentNames = jvmSimpleName <$> args
        let argIndices = getArgumentIndices arityInt argumentNames
        let initialArgumentTypes = replicate arity IUnknown
        let argumentTypesByName = SortedMap.fromList $ List.zip argumentNames initialArgumentTypes
        let function = MkFunction jname (MkInferredFunctionType IUnknown initialArgumentTypes)
            SortedMap.empty 0 jvmClassAndMethodName tailCallCategory (NmCrash emptyFC "uninitialized function")
        setCurrentFunction function
        updateState $ record { functions $= SortedMap.insert jname function }
        optimizedExpr <- optimize tailCallCategory expr
        debug $ "Inferring " ++ show idrisName
        updateCurrentFunction $ record { optimizedBody = optimizedExpr }

        resetScope
        scopeIndex <- newScopeIndex
        let (_, lineStart, lineEnd) = getSourceLocation expr
        let functionScope = MkScope scopeIndex Nothing argumentTypesByName SortedMap.empty argIndices SortedMap.empty
            IUnknown arityInt (lineStart, lineEnd) ("", "") []

        saveScope functionScope
        retTy <- inferExpr IUnknown optimizedExpr
        updateScopeVariableTypes
        let inferredFunctionType = MkInferredFunctionType retTy !(getArgumentTypes argumentNames)
        updateCurrentFunction $ record { inferredFunctionType = inferredFunctionType }
    where
        getArgumentTypes : List String -> Asm (List InferredType)
        getArgumentTypes argumentNames = do
            argumentIndicesByName <- getVariableIndicesByName 0
            argumentTypesByIndex <- getVariableTypesAtScope 0
            Pure $ go argumentIndicesByName argumentTypesByIndex argumentNames
          where
            go : SortedMap String Int -> SortedMap Int InferredType -> List String -> List InferredType
            go argumentIndicesByName argumentTypesByIndex argumentNames = reverse $ go1 [] argumentNames where
                go1 : List InferredType -> List String -> List InferredType
                go1 acc [] = acc
                go1 acc (arg :: args) =
                    let ty = fromMaybe IUnknown $ do
                                index <- SortedMap.lookup arg argumentIndicesByName
                                SortedMap.lookup index argumentTypesByIndex
                    in go1 (ty :: acc) args

inferDef n fc (MkNmError expr) = inferDef n fc (MkNmFun [] expr)

inferDef idrisName fc def@(MkNmForeign foreignDescriptors argumentTypes returnType) =
    inferForeign idrisName fc foreignDescriptors argumentTypes returnType

inferDef n _ def = Pure ()