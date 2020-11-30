module Compiler.Jvm.Optimizer

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.Bool.Extra
import Data.SortedMap
import Data.Vect

import Compiler.Jvm.InferredType
import Compiler.Jvm.Jname
import Compiler.Jvm.Jvar
import Compiler.Jvm.Asm
import Compiler.Jvm.ExtPrim
import Compiler.Jvm.ShowUtil
import Compiler.Jvm.Foreign

%access public export

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

hasBranch : NamedCExp -> Bool
hasBranch (NmLet _ var value sc) = hasBranch value || hasBranch sc
hasBranch (NmApp _ f args) = hasBranch f || anyTrue (map hasBranch args)
hasBranch (NmCon _ _ _ args) = anyTrue (map hasBranch args)
hasBranch (NmOp _ (LT _) _) = True
hasBranch (NmOp _ (LTE _) _) = True
hasBranch (NmOp _ (EQ _) _) = True
hasBranch (NmOp _ (GTE _) _) = True
hasBranch (NmOp _ (GT _) _) = True
hasBranch (NmOp _ _ args) = anyTrue (toList (map hasBranch args))
hasBranch (NmExtPrim _ _ args) = anyTrue (map hasBranch args)
hasBranch (NmForce _ t) = hasBranch t
hasBranch (NmConCase _ sc alts def) = True
hasBranch (NmConstCase _ sc alts def) = True
hasBranch _ = False

tySpec : NamedCExp -> Asm InferredType
tySpec (NmCon fc (UN "Int") _ []) = pure IInt
tySpec (NmCon fc (UN "String") _ []) = pure inferredStringType
tySpec (NmCon fc (UN "Double") _ []) = pure IDouble
tySpec (NmCon fc (UN "Char") _ []) = pure IChar
tySpec (NmCon fc (UN "Bool") _ []) = pure IBool
tySpec (NmCon fc (UN "void") _ []) = pure IVoid
tySpec (NmCon fc (UN ty) _ []) = pure $ IRef ty
tySpec (NmCon fc (NS _ n) _ [])
     = cond [(n == UN "Unit", pure IVoid)]
          (Throw fc ("Can't pass argument of type " ++ show n ++ " to foreign function"))
tySpec ty = Throw (getFC ty) ("Can't pass argument of type " ++ show ty ++ " to foreign function")

getFArgs : NamedCExp -> Asm (List (NamedCExp, NamedCExp))
getFArgs (NmCon fc _ (Just 0) _) = pure []
getFArgs (NmCon fc _ (Just 1) [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
getFArgs arg = Throw (getFC arg) ("Badly formed jvm call argument list " ++ show arg)

getLineNumbers : FilePos -> FilePos -> (Int, Int)
getLineNumbers (lineStart, _) (lineEnd, colEnd) =
    (lineStart + 1, if colEnd == 1 then lineEnd else lineEnd + 1)

getSourceLocation : NamedCExp -> (String, Int, Int)
getSourceLocation expr = case getFC expr of
    EmptyFC => case expr of
        (NmExtPrim _ _ (arg :: args)) => getSourceLocation arg
        (NmOp _ _ (arg :: _)) => getSourceLocation arg
        _ => ("Main.idr", 1, 1)
    (MkFC fileName startPos endPos) =>
        (fileName, getLineNumbers startPos endPos)

getSourceLocationFromFc : FC -> (String, Int, Int)
getSourceLocationFromFc EmptyFC = ("Main.idr", 1, 1)
getSourceLocationFromFc (MkFC fileName startPos endPos) = (fileName, getLineNumbers startPos endPos)

mutual
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

mutual
    doGetUsageCount : Nat -> Name -> NamedCExp -> Nat
    doGetUsageCount count name (NmLocal fc var) = if name == var then count + 1 else count
    doGetUsageCount count name (NmRef _ _) = count
    doGetUsageCount count name (NmLam _ _ sc) = doGetUsageCount count name sc
    doGetUsageCount count name (NmLet _ var value sc) =
        let usageCountInValue = doGetUsageCount count name value
        in doGetUsageCount usageCountInValue name sc
    doGetUsageCount count name (NmApp _ f args) = foldl (\acc, arg => doGetUsageCount acc name arg) count args
    doGetUsageCount count name (NmCon _ _ _ args) = foldl (\acc, arg => doGetUsageCount acc name arg) count args
    doGetUsageCount count name (NmOp _ _ args) = foldl (\acc, arg => doGetUsageCount acc name arg) count args
    doGetUsageCount count name (NmExtPrim _ _ args) = foldl (\acc, arg => doGetUsageCount acc name arg) count args
    doGetUsageCount count name (NmForce _ t) = doGetUsageCount count name t
    doGetUsageCount count name (NmDelay _ t) = doGetUsageCount count name t
    doGetUsageCount count name (NmConCase _ sc alts def) =
        let altsCount = foldl (\acc, alt => doGetUsageCountCon acc name alt) (doGetUsageCount count name sc) alts
        in maybe altsCount (doGetUsageCount altsCount name) def
    doGetUsageCount count name (NmConstCase _ sc alts def) =
        let altsCount = foldl (\acc, alt => doGetUsageCountConst acc name alt) (doGetUsageCount count name sc) alts
        in maybe altsCount (doGetUsageCount altsCount name) def
    doGetUsageCount count name _ = count

    doGetUsageCountCon : Nat -> Name -> NamedConAlt -> Nat
    doGetUsageCountCon count name (MkNConAlt _ _ _ sc) = doGetUsageCount count name sc

    doGetUsageCountConst : Nat -> Name -> NamedConstAlt -> Nat
    doGetUsageCountConst count name (MkNConstAlt _ sc) = doGetUsageCount count name sc

getUsageCount : Name -> NamedCExp -> Nat
getUsageCount name expr = doGetUsageCount 0 name expr

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
    trampolineExpression expr@(NmApp fc (NmRef nameFc idrisName) args) = Pure $ NmDelay fc expr
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
    inlineVariable var value (NmApp fc f args) =
        NmApp fc f (inlineVariable var value <$> args)
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
        if getUsageCount var body == 1 then
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

exitInferenceScope : Scope -> Asm ()
exitInferenceScope targetScope = updateCurrentScopeIndex (index targetScope)

enterInferenceScope : Int -> Int -> Asm ()
enterInferenceScope lineNumberStart lineNumberEnd = do
    parentScopeIndex <- getCurrentScopeIndex
    scopeIndex <- freshScopeIndex
    parentScope <- getScope parentScopeIndex
    let newScope = MkScope scopeIndex (Just parentScopeIndex) SortedMap.empty SortedMap.empty IUnknown
        (nextVariableIndex parentScope) (lineNumberStart, lineNumberEnd) ("", "") []
    addScopeChild parentScopeIndex scopeIndex
    updateScope scopeIndex newScope
    updateCurrentScopeIndex scopeIndex

createLambdaClosureScope : Nat -> Nat -> List String -> Scope -> Asm Scope
createLambdaClosureScope scopeIndex childScopeIndex closureVariables parentScope = do
        let lambdaClosureVariableIndices = SortedMap.fromList $ getLambdaClosureVariableIndices [] 0 closureVariables
        Pure $ MkScope scopeIndex (Just $ index parentScope) SortedMap.empty lambdaClosureVariableIndices IUnknown
                (length closureVariables) (lineNumbers parentScope) ("", "") [childScopeIndex]
    where
        getLambdaClosureVariableIndices : List (String, Nat) -> Nat -> List String -> List (String, Nat)
        getLambdaClosureVariableIndices acc _ [] = acc
        getLambdaClosureVariableIndices acc index (var :: vars) = 
            getLambdaClosureVariableIndices ((var, index) :: acc) (index + 1) vars

enterInferenceLambdaScope : Int -> Int -> List String -> NamedCExp -> Asm ()
enterInferenceLambdaScope lineNumberStart lineNumberEnd lambdaParameters expr = do
        parentScopeIndex <- getCurrentScopeIndex
        scopeIndex <- freshScopeIndex
        parentScope <- getScope parentScopeIndex
        let usedVariables = filter (flip used expr) !(getVariables parentScopeIndex)
        newScope <- case usedVariables  of
            nonEmptyUsedVariables@(_ :: _) => do
                lambdaParentScopeIndex <- freshScopeIndex
                closureScope <- createLambdaClosureScope lambdaParentScopeIndex scopeIndex nonEmptyUsedVariables
                    parentScope
                updateScope lambdaParentScopeIndex closureScope
                let closureVariableCount = nextVariableIndex closureScope
                Pure $ MkScope scopeIndex (Just lambdaParentScopeIndex) SortedMap.empty
                    SortedMap.empty IUnknown closureVariableCount (lineNumberStart, lineNumberEnd) ("", "") []
            [] => Pure $ MkScope scopeIndex Nothing SortedMap.empty SortedMap.empty
                IUnknown 0 (lineNumberStart, lineNumberEnd) ("", "") []
        updateScope scopeIndex newScope
        updateCurrentScopeIndex scopeIndex
        traverse_ createVariable lambdaParameters
        traverse_ (flip addVariableType inferredObjectType) lambdaParameters

withInferenceScope : Int -> Int -> Asm result -> Asm result
withInferenceScope lineNumberStart lineNumberEnd op = do
    scope <- getScope !getCurrentScopeIndex
    enterInferenceScope lineNumberStart lineNumberEnd
    result <- op
    exitInferenceScope scope
    Pure result

withInferenceLambdaScope : Int -> Int -> List String -> NamedCExp -> Asm result -> Asm result
withInferenceLambdaScope lineNumberStart lineNumberEnd lambdaParameters expr op = do
    scope <- getScope !getCurrentScopeIndex
    enterInferenceLambdaScope lineNumberStart lineNumberEnd lambdaParameters expr
    result <- op
    exitInferenceScope scope
    Pure result

getLambdaInterfaceType : (param : Maybe Name) -> InferredType -> InferredType
getLambdaInterfaceType Nothing returnType = getThunkType returnType
getLambdaInterfaceType _ returnType = inferredLambdaType

getConstantType : List NamedConstAlt -> Asm InferredType
getConstantType [] = Throw emptyFC "Unknown constant switch type"
getConstantType ((MkNConstAlt constant _) :: _) = case constant of
    I _ => Pure IInt
    Ch _ => Pure IInt
    Str _ => Pure inferredStringType
    BI _ => Pure inferredBigIntegerType
    unsupportedConstant => Throw emptyFC $ "Unsupported constant switch " ++ show unsupportedConstant

isTypeConst : TT.Constant -> Bool
isTypeConst IntType     = True
isTypeConst IntegerType = True
isTypeConst StringType  = True
isTypeConst CharType    = True
isTypeConst DoubleType  = True
isTypeConst WorldType   = True
isTypeConst _           = False

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

mutual
    public export
    inferExpr : InferredType -> NamedCExp -> Asm InferredType
    inferExpr exprTy (NmDelay _ expr) = inferExprLam Nothing expr
    inferExpr exprTy expr@(NmLocal _ var) = addVariableType (jvmSimpleName var) exprTy
    inferExpr exprTy (NmRef _ _) = pure exprTy
    inferExpr _ (NmLam _ var body) = inferExprLam (Just var) body
    inferExpr exprTy (NmLet fc var value expr) = inferExprLet fc exprTy var value expr
    inferExpr exprTy app@(NmApp _ (NmRef _ _) _) = inferExprApp exprTy app
    inferExpr exprTy app@(NmApp _ var _) = do
        inferExpr inferredLambdaType var
        inferExprApp exprTy app
    inferExpr exprTy expr@(NmCon fc name tag args) =
        inferExprCon exprTy (fst $ getSourceLocation expr) name args
    inferExpr exprTy (NmOp _ fn args) = inferExprOp fn args
    inferExpr exprTy (NmExtPrim _ fn args) = inferExtPrim exprTy (toPrim fn) args
    inferExpr exprTy (NmForce _ expr) = inferExpr thunkType expr

    inferExpr exprTy (NmConCase _ sc [] Nothing) = Pure IUnknown
    inferExpr exprTy (NmConCase _ sc [] (Just def)) = do
        idrisObjectVariable <- generateVariable "constructorSwitchValue"
        inferExpr idrisObjectType sc
        addVariableType idrisObjectVariable idrisObjectType
        inferExpr exprTy def
    inferExpr exprTy (NmConCase _ sc [MkNConAlt _ _ args expr] Nothing) = do
        idrisObjectVariable <- generateVariable "constructorSwitchValue"
        inferExpr idrisObjectType sc
        addVariableType idrisObjectVariable idrisObjectType
        inferConCaseExpr exprTy args expr
    inferExpr exprTy (NmConCase _ sc alts def) = do
        idrisObjectVariable <- generateVariable "constructorSwitchValue"
        inferExpr idrisObjectType sc
        addVariableType idrisObjectVariable idrisObjectType
        let sortedAlts = sortConCases alts
        altTypes <- traverse (inferExprConAlt exprTy) sortedAlts
        defTy <- maybe (Pure IUnknown) (inferExprWithNewScope exprTy) def
        let switchResultType = foldl (<+>) IUnknown (defTy :: altTypes)
        Pure switchResultType

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
        defTy <- maybe (Pure IUnknown) (inferExprWithNewScope exprTy) def
        let switchResultType = foldl (<+>) IUnknown (defTy :: altTypes)
        Pure switchResultType
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
        boolOpResultVariable <- generateVariable "jvm$boolOpResult"
        addVariableType boolOpResultVariable IBool
        inferExpr ty x
        inferExpr ty y
        pure IBool

    inferUnaryOp : InferredType -> NamedCExp -> Asm InferredType
    inferUnaryOp ty x = do inferExpr ty x; Pure ty

    inferExtPrimArg : (NamedCExp, InferredType) -> Asm InferredType
    inferExtPrimArg (arg, ty) = inferExpr ty arg

    inferExtPrim : InferredType -> ExtPrim -> List NamedCExp -> Asm InferredType
    inferExtPrim returnType JvmStaticMethodCall [ret, NmPrimVal fc (Str fn), fargs, world]
      = do args <- getFArgs fargs
           argTypes <- traverse tySpec (map fst args)
           methodReturnType <- tySpec ret
           traverse inferExtPrimArg $ List.zip (map snd args) argTypes
           let (cname, mnameWithDot) = break (== '.') fn
           let (_, mname) = break (/= '.') mnameWithDot
           pure methodReturnType
    inferExtPrim _ prim args = Throw emptyFC ("Unsupported external function " ++ show prim)

    inferExprLam : (param : Maybe Name) -> NamedCExp -> Asm InferredType
    inferExprLam param expr = do
        let (_, lineStart, lineEnd) = getSourceLocation expr
        let parameterNames = jvmSimpleName <$> toList param
        lambdaBodyReturnType <- withInferenceLambdaScope lineStart lineEnd parameterNames expr $ do
            lambdaBodyReturnType <- inferExpr IUnknown expr
            currentScope <- getScope !getCurrentScopeIndex
            updateScope (index currentScope) $ record {returnType = lambdaBodyReturnType} currentScope
            Pure lambdaBodyReturnType
        Pure $ getLambdaInterfaceType param lambdaBodyReturnType

    inferExprLet : FC -> InferredType -> (x : Name) -> NamedCExp -> NamedCExp -> Asm InferredType
    inferExprLet fc exprTy var value expr = do
        let (lineStart, lineEnd) = getLineNumbers (startPos fc) (endPos fc)
        withInferenceScope lineStart lineEnd $ do
            let varName = jvmSimpleName var
            createVariable varName
            let (_, lineStart, lineEnd) = getSourceLocation value
            valueTy <- withInferenceScope lineStart lineEnd $ inferExpr IUnknown value

            addVariableType varName valueTy

            let (_, lineStart, lineEnd) = getSourceLocation expr
            retTy <- withInferenceScope lineStart lineEnd $ inferExpr exprTy expr

            pure retTy

    inferSelfTailCallParameter : SortedMap Nat InferredType -> (NamedCExp, Nat) -> Asm InferredType
    inferSelfTailCallParameter types (arg, index) = do
        let variableType = fromMaybe IUnknown $ SortedMap.lookup index types
        inferExpr variableType arg

    inferExprApp : InferredType -> NamedCExp -> Asm InferredType
    inferExprApp exprTy app@(NmApp _ (NmRef _ (UN ":__jvmTailRec__:")) args) =
        case args of
            [] => Pure exprTy
            args@(_ :: argsTail) => do
                types <- getVariableTypes
                traverse (inferSelfTailCallParameter types) $ List.zip args [0 .. length argsTail]
                Pure exprTy
    inferExprApp exprTy (NmApp _ (NmRef _ idrisName) args) = do
        let functionName = jvmName idrisName
        let functionType = fromMaybe (MkInferredFunctionType IUnknown $ replicate (length args) IUnknown)
            !(findFunctionType functionName)
        let argsWithTypes = List.zip args (parameterTypes functionType)
        traverse_ inferParameter argsWithTypes
        Pure $ returnType functionType
    inferExprApp exprTy (NmApp _ lambdaVariable args) = do
        let argsWithTypes = List.zip args (replicate (length args) IUnknown)
        traverse_ inferParameter argsWithTypes
        pure IUnknown

    inferExprCon : InferredType -> String -> Name -> List NamedCExp -> Asm InferredType
    inferExprCon exprTy fileName name args = do
        let jname = jvmName name
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
    {-inferExprOp  is Euler's number, which approximates to: 2.718281828459045
    inferExprOp DoubleExp [x] = op "expr" [x] -- Base is `e`. Same as: `pow(e, x)`
    inferExprOp DoubleLog [x] = op "log" [x] -- Base is `e`.
    inferExprOp DoubleSin [x] = op "sin" [x]
    inferExprOp DoubleCos [x] = op "cos" [x]
    inferExprOp DoubleTan [x] = op "tan" [x]
    inferExprOp DoubleASin [x] = op "asin" [x]
    inferExprOp DoubleACos [x] = op "acos" [x]
    inferExprOp DoubleATan [x] = op "atan" [x]
    inferExprOp DoubleSqrt [x] = op "sqrt" [x]
    inferExprOp DoubleFloor [x] = op "floor" [x]
    inferExprOp DoubleCeiling [x] = op "ceiling" [x]-}

    inferExprOp (Cast IntType StringType) [x] = do
        inferExpr IInt x
        pure inferredStringType
    inferExprOp (Cast IntegerType StringType) [x] = do
        inferExpr inferredBigIntegerType x
        pure inferredStringType
    {-inferExprOp (Cast DoubleType StringType) [x] = op "number->string" [x]
    inferExprOp (Cast CharType StringType) [x] = op "string" [x]-}

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
    inlinedAndTailRecursionMarkedExpr <- markTailRecursion (eliminateSingleUsageVariable expr)
    if hasNonSelfTailCall tailCallCategory then trampolineExpression inlinedAndTailRecursionMarkedExpr
    else Pure inlinedAndTailRecursionMarkedExpr

inferDef : Name -> FC -> NamedDef -> Asm ()
inferDef idrisName fc (MkNmFun args expr) = do
        let jname = jvmName idrisName
        let hasSelfTailCall = hasTailCall (== idrisName) expr
        let hasNonSelfTailCall = hasTailCall (/= idrisName) expr
        let fileName = fst $ getSourceLocationFromFc fc
        let jvmClassAndMethodName = getIdrisFunctionName (className jname) fileName (methodName jname)
        let tailCallCategory = MkTailCallCategory hasSelfTailCall hasNonSelfTailCall
        let function = MkFunction jname (MkInferredFunctionType IUnknown []) SortedMap.empty 0 jvmClassAndMethodName
            tailCallCategory (NmCrash emptyFC "uninitialized function") False
        setCurrentFunction function
        updateState $ record { functions $= SortedMap.insert jname function }
        optimizedExpr <- optimize tailCallCategory expr
        let needResultVariable = hasSelfTailCall || hasBranch optimizedExpr
        updateCurrentFunction $ record { optimizedBody = optimizedExpr, needResultVariable = needResultVariable }

        resetScope
        let arity = length args
        let argumentNames = jvmSimpleName <$> args
        let argIndices = getArgumentIndices arity argumentNames
        let argInitialTypes = SortedMap.fromList $ List.zip argumentNames $ replicate arity IUnknown
        scopeIndex <- freshScopeIndex
        let (_, lineStart, lineEnd) = getSourceLocation expr
        let functionScope = MkScope scopeIndex Nothing argInitialTypes argIndices IUnknown arity
            (lineStart, lineEnd) ("", "") []

        updateScope scopeIndex functionScope
        resultVariable <- if needResultVariable then generateVariable "jvm$fn$res" else Pure ""
        when hasSelfTailCall $ do
            tailRecursionLoopVariable <- generateVariable "jvm$rec$loop"
            addVariableType tailRecursionLoopVariable IInt
            Pure ()

        retTy <- inferExpr IUnknown optimizedExpr
        when needResultVariable $ do
            addVariableType resultVariable $ if retTy == IVoid then inferredObjectType else retTy
            Pure ()
        argumentTypes <- getArgumentTypes argumentNames
        let inferredFunctionType = MkInferredFunctionType retTy argumentTypes
        updateCurrentFunction $ record { inferredFunctionType = inferredFunctionType }
    where
        getArgumentTypes : List String -> Asm (List InferredType)
        getArgumentTypes [] = pure []
        getArgumentTypes (arg :: args) = do
            argTy <- getVariableType arg
            argTys <- getArgumentTypes args
            Pure (argTy :: argTys)

inferDef n fc (MkNmError expr) = inferDef n fc (MkNmFun [] expr)

inferDef idrisName fc def@(MkNmForeign foreignDescriptors argumentTypes returnType) =
    inferForeign idrisName fc foreignDescriptors argumentTypes returnType

inferDef n _ def = Pure ()