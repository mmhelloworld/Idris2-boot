module Compiler.Jvm.Core

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

import IdrisJvm.IO

import Compiler.Jvm.Asm
import Compiler.Jvm.FunctionTree

%default covering

export
firstExists : List String -> JVM_IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

schString : String -> String
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

export
schName : Name -> String
schName (NS ns n) = showSep "-" ns ++ "-" ++ schName n
schName (UN n) = schString n
schName (MN n i) = schString n ++ "-" ++ show i
schName (PV n d) = "pat--" ++ schName n
schName (DN _ n) = schName n
schName (Nested i n) = "n--" ++ show i ++ "-" ++ schName n
schName (CaseBlock x y) = "case--" ++ show x ++ "-" ++ show y
schName (WithBlock x y) = "with--" ++ show x ++ "-" ++ show y
schName (Resolved i) = "fn--" ++ show i

-- local variable names as scheme names - we need to invent new names for the locals
-- because there might be shadows in the original expression which can't be resolved
-- by the same scoping rules. (e.g. something that computes \x, x => x + x where the
-- names are the same but refer to different bindings in the scope)
public export
data SVars : List Name -> Type where
     Nil : SVars []
     (::) : (svar : String) -> SVars ns -> SVars (n :: ns)

extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
  where
    extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
    extSVars' i [] vs = vs
    extSVars' i (x :: xs) vs = schName (MN "v" i) :: extSVars' (i + 1) xs vs

export
initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : {idx : Nat} -> .(IsVar n idx xs) -> SVars xs -> String
lookupSVar First (n :: ns) = n
lookupSVar (Later p) (n :: ns) = lookupSVar p ns

export
schConstructor : Name -> Int -> List String -> String
schConstructor name t args =
    let jname = jvmName name
        clsName = className jname
        constructorName = methodName jname
    in instructions [
        ["iconst", show t],
        [showSep lineSeparator args],
        ["makeConstructor", clsName, constructorName, show $ length args]
    ]

||| Generate scheme for a plain function.
op : String -> List String -> String
op o args = showSep lineSeparator args ++ lineSeparator ++ o

||| Generate scheme for a boolean operation.
boolop : String -> List String -> String
boolop o args = op o args

||| Extended primitives for the scheme backend, outside the standard set of primFn
public export
data ExtPrim = CCall | SchemeCall | PutStr | GetStr
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | Stdin | Stdout | Stderr
             | VoidElim | Unknown Name

export
Show ExtPrim where
  show CCall = "CCall"
  show SchemeCall = "SchemeCall"
  show PutStr = "PutStr"
  show GetStr = "GetStr"
  show FileOpen = "FileOpen"
  show FileClose = "FileClose"
  show FileReadLine = "FileReadLine"
  show FileWriteLine = "FileWriteLine"
  show FileEOF = "FileEOF"
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show Stdin = "Stdin"
  show Stdout = "Stdout"
  show Stderr = "Stderr"
  show VoidElim = "VoidElim"
  show (Unknown n) = "Unknown " ++ show n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN "prim__schemeCall", SchemeCall),
            (n == UN "prim__cCall", CCall),
            (n == UN "prim__putStr", PutStr),
            (n == UN "prim__getStr", GetStr),
            (n == UN "prim__open", FileOpen),
            (n == UN "prim__close", FileClose),
            (n == UN "prim__readLine", FileReadLine),
            (n == UN "prim__writeLine", FileWriteLine),
            (n == UN "prim__eof", FileEOF),
            (n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef),
            (n == UN "prim__stdin", Stdin),
            (n == UN "prim__stdout", Stdout),
            (n == UN "prim__stderr", Stderr),
            (n == UN "void", VoidElim)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : String -> String
mkWorld res = schConstructor (NS ["PrimIO"] (UN "MkIORes")) 0
                [instruction ["iconst", "0"], res, instruction ["iconst", "0"]] -- MkIORes

schConstant : (String -> String) -> Constant -> String
schConstant _ (I x) = instruction ["iconst", show x]
schConstant _ (BI x) = newBigInteger $ show x
schConstant schString (Str x) = schString x
schConstant _ (Ch x) = instruction ["iconst", show $ cast {to=Int} x]
schConstant _ (Db x) = instruction ["ldc", "DoubleConst", show x]
schConstant _ WorldVal = instruction ["iconst", "0"]
schConstant _ IntType = instruction ["iconst", "1"]
schConstant _ IntegerType = instruction ["iconst", "1"]
schConstant _ StringType = instruction ["iconst", "1"]
schConstant _ CharType = instruction ["iconst", "1"]
schConstant _ DoubleType = instruction ["iconst", "1"]
schConstant _ WorldType = instruction ["iconst", "1"]

schCaseDef : Maybe String -> String
schCaseDef Nothing = ""
schCaseDef (Just tm) = "defaultCase" ++ lineSeparator ++ tm

export
schArglist : SVars ns -> String
schArglist [] = ""
schArglist [x] = x
schArglist (x :: xs) = x ++ " " ++ schArglist xs

constructorClass : CConAlt vars -> String
constructorClass (MkConAlt n _ _ _) = className $ jvmName n

binaryOp : InferredType -> (InferredType -> Asm ()) -> Asm () -> LVar -> LVar -> Asm ()
binaryOp ty ret ops l r = do
  locTypes <- GetFunctionLocTypes
  let lTy = getLocTy locTypes l
  let rTy = getLocTy locTypes r
  loadVar locTypes lTy ty l
  loadVar locTypes rTy ty r
  ops
  ret ty

parameters (schExtPrim : {vars : _} -> Int -> Jvars vars -> ExtPrim -> List (CExp vars) -> Core String,
            schString : String -> String)
  mutual
    schOp : (InferredType -> Asm ()) -> Int -> Jvars vars -> PrimFn arity -> Vect arity (CExp vars) -> String
    schOp ret i vs (Add IntType) [x, y] = do
        schArgs ret i vs [(x, IInt), (y, IInt)]
        binaryOp IInt ret Iadd
    schOp (Sub IntType) [x, y] = op "isub" [x, y]
    schOp (Mul IntType) [x, y] = op "imul" [x, y]
    schOp (Div IntType) [x, y] = op "idiv" [x, y]
    schOp (Add ty) [x, y] = op "+" [x, y]
    schOp (Sub ty) [x, y] = op "-" [x, y]
    schOp (Mul ty) [x, y] = op "*" [x, y]
    schOp (Div ty) [x, y] = op "/" [x, y]
    schOp (Mod ty) [x, y] = op "remainder" [x, y]
    schOp (Neg ty) [x] = op "-" [x]
    schOp (ShiftL ty) [x, y] = op "blodwen-shl" [x, y]
    schOp (ShiftR ty) [x, y] = op "blodwen-shr" [x, y]
    schOp (LT CharType) [x, y] = boolop "char<?" [x, y]
    schOp (LTE CharType) [x, y] = boolop "char<=?" [x, y]
    schOp (EQ CharType) [x, y] = boolop "char=?" [x, y]
    schOp (GTE CharType) [x, y] = boolop "char>=?" [x, y]
    schOp (GT CharType) [x, y] = boolop "char>?" [x, y]
    schOp (LT StringType) [x, y] = boolop "string<?" [x, y]
    schOp (LTE StringType) [x, y] = boolop "string<=?" [x, y]
    schOp (EQ StringType) [x, y] = boolop "string=?" [x, y]
    schOp (GTE StringType) [x, y] = boolop "string>=?" [x, y]
    schOp (GT StringType) [x, y] = boolop "string>?" [x, y]
    schOp (LT ty) [x, y] = boolop "<" [x, y]
    schOp (LTE ty) [x, y] = boolop "<=" [x, y]
    schOp (EQ ty) [x, y] = boolop "=" [x, y]
    schOp (GTE ty) [x, y] = boolop ">=" [x, y]
    schOp (GT ty) [x, y] = boolop ">" [x, y]
    schOp StrLength [x] = op "string-length" [x]
    schOp StrHead [x] = op "string-ref" [x, "0"]
    schOp StrTail [x] = op "substring" [x, "1", op "string-length" [x]]
    schOp StrIndex [x, i] = op "string-ref" [x, i]
    schOp StrCons [x, y] = op "string-cons" [x, y]
    schOp StrAppend [x, y] = op "string-append" [x, y]
    schOp StrReverse [x] = op "string-reverse" [x]
    schOp StrSubstr [x, y, z] = op "string-substr" [x, y, z]

    -- `e` is Euler's number, which approximates to: 2.718281828459045
    schOp DoubleExp [x] = op "exp" [x] -- Base is `e`. Same as: `pow(e, x)`
    schOp DoubleLog [x] = op "log" [x] -- Base is `e`.
    schOp DoubleSin [x] = op "sin" [x]
    schOp DoubleCos [x] = op "cos" [x]
    schOp DoubleTan [x] = op "tan" [x]
    schOp DoubleASin [x] = op "asin" [x]
    schOp DoubleACos [x] = op "acos" [x]
    schOp DoubleATan [x] = op "atan" [x]
    schOp DoubleSqrt [x] = op "sqrt" [x]
    schOp DoubleFloor [x] = op "floor" [x]
    schOp DoubleCeiling [x] = op "ceiling" [x]

    schOp (Cast IntType StringType) [x] = op "number->string" [x]
    schOp (Cast IntegerType StringType) [x] = op "number->string" [x]
    schOp (Cast DoubleType StringType) [x] = op "number->string" [x]
    schOp (Cast CharType StringType) [x] = op "string" [x]

    schOp (Cast IntType IntegerType) [x] = x
    schOp (Cast DoubleType IntegerType) [x] = op "floor" [x]
    schOp (Cast CharType IntegerType) [x] = op "char->integer" [x]
    schOp (Cast StringType IntegerType) [x] = op "cast-string-int" [x]

    schOp (Cast IntegerType IntType) [x] = x
    schOp (Cast DoubleType IntType) [x] = op "floor" [x]
    schOp (Cast StringType IntType) [x] = op "cast-string-int" [x]
    schOp (Cast CharType IntType) [x] = op "char->integer" [x]

    schOp (Cast IntegerType DoubleType) [x] = op "exact->inexact" [x]
    schOp (Cast IntType DoubleType) [x] = op "exact->inexact" [x]
    schOp (Cast StringType DoubleType) [x] = op "cast-string-double" [x]

    schOp (Cast IntType CharType) [x] = op "integer->char" [x]

    schOp (Cast from to) [x] = "(blodwen-error-quit \"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"

    schOp BelieveMe [_,_,x] = x

    schConAlt : {auto assembler : Assembler} -> Int -> Jvars vars -> Nat -> CConAlt vars -> Core String
    schConAlt {vars} i vs idrisObj (MkConAlt n tag args sc) = do
        let vs' = extendJvars i args vs
        pure $ instructions [
            ["case", show tag],
            [bindArgs 1 args vs' !(schExp i vs' sc)],
            ["endCase"]
         ]
      where
        idrisObjClass : String
        idrisObjClass = className $ jvmName n

        bindArgs : Int -> (ns : List Name) -> Jvars (ns ++ vars) -> String -> String
        bindArgs i [] vs body = body
        bindArgs i (n :: ns) (v :: vs) body = instructions [
            ["aload", show idrisObj],
            ["field", "get", idrisObjClass, "p" ++ show i, "Ljava/lang/Object;"],
            ["astore", show (jvarIndex v)],
            [bindArgs (i + 1) ns vs body]
        ]

    schConstAlt : {auto assembler : Assembler} -> Int -> Jvars vars -> Nat -> CConstAlt vars -> Core String
    schConstAlt i vs ifExpr (MkConstAlt c exp) =
        pure $ instructions [
            ["ifCase"],
            ["aload", show ifExpr],
            [schConstant schString c],
            ["invokeStatic", "java/util/Objects", "equals", "(Ljava/lang/Object;Ljava/lang/Object;)Z", "false"],
            ["then"],
            [!(schExp i vs exp)],
            ["endIfCase"]
        ]

    -- oops, no traverse for Vect in Core
    schArgs : (InferredType -> Asm ()) -> Int -> Jvars vars -> Vect n (CExp vars, InferredType) -> Asm ()
    schArgs ret i vs [] = pure ()
    schArgs ret i vs ((arg, ty) :: args) = do
        schExp ret i vs ty arg
        schArgs ret i vs args

    export
    schExp : Int -> Jvars vars -> InferredType -> CExp vars -> Asm ()
    schExp i vs exprTy (CLocal fc el) = do
        let var = lookupJvar el vs
        updateLocalVarType (jvarIndex var) exprTy
        pure $ aload fc var
    schExp i vs (CLam fc x sc) = do
        let vs' = extendJvars i [x] vs
        sc' <- schExp vs' sc
        pure $ lambda fc vs sc'
    schExp i vs (CLet fc x val sc) = do
        val' <- schExp i vs val
        let vs' = extendJvars i [x] vs
        sc' <- schExp (i + 1) vs' sc
        pure $ astore fc (lookupJvar First vs') val' ++ lineSeparator ++ sc'
    schExp i vs (CApp fc (CRef _ f) args) =
        let loadedArgs = showSep lineSeparator !(traverse (schExp i vs) args)
            nArgs = length args
            jname = jvmName f
        in pure $ loadedArgs ++ lineSeparator ++ instruction ["call", className jname, methodName jname, show nArgs]
    schExp i vs (CApp fc f args) =
        let loadedArgs = showSep lineSeparator !(traverse (schExp i vs) args)
            loadedLambdaVar = instructions [
                [!(schExp i vs f)],
                ["cast", "java/util/function/Function"]
            ]
        in pure $ loadedLambdaVar ++ lineSeparator ++ loadedArgs ++ lineSeparator ++ "applyLambda"
    schExp i vs (CCon fc name tag args)
        = pure $ schConstructor name tag !(traverse (schExp i vs) args)
    schExp i vs (COp fc op args) = schOp i vs op args
    schExp i vs (CExtPrim fc p args)
        = schExtPrim i vs (toPrim p) args
    schExp i vs (CForce fc t) = pure $ showSep lineSeparator [!(schExp i vs t), "force"]
    schExp i vs (CDelay fc t) = pure $ showSep lineSeparator [!(schExp i vs t), "delay"]
    schExp i vs (CConCase fc sc alts@(alt::_) def)
        = do tcode <- schExp (i+1) vs sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i vs v))) def
             let idrisObj = MkJvar ("sc" ++ show i) (cast i)
             let idrisObjIndex = jvarIndex idrisObj
             let idrisObjClass = constructorClass alt
             pure $ instructions [
                [astore fc idrisObj tcode],
                ["aload", show idrisObjIndex],
                ["field", "get", idrisObjClass, "constructorId", "I"],
                ["lookupSwitch"],
                [showSep lineSeparator !(traverse (schConAlt (i+1) vs idrisObjIndex) alts)],
                [schCaseDef defc],
                ["endLookupSwitch"]
            ]
    schExp i vs (CConstCase fc sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i vs v))) def
             tcode <- schExp (i+1) vs sc
             let ifExpr = MkJvar ("if" ++ show i) (cast i)
             pure $ instructions [
                [astore fc ifExpr tcode],
                ["if"],
                [showSep lineSeparator !(traverse (schConstAlt (i+1) vs (jvarIndex ifExpr)) alts)],
                [schCaseDef defc],
                ["endIf"]
             ]
    schExp i vs (CPrimVal fc c) = pure $ schConstant schString c
    schExp i vs (CErased fc) = pure "erased"
    schExp i vs (CCrash fc msg) = pure $ "error " ++ show msg ++ ")"
    schExp i vs expr = pure $ "error " ++ show expr

  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : {auto assembler : Assembler} -> Int -> Jvars vars -> CExp vars -> Core String
  readArgs i vs tm = pure $ "(blodwen-read-args " ++ !(schExp i vs tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : {auto assembler : Assembler} -> Int -> Jvars vars -> ExtPrim -> List (CExp vars) -> Core String
  schExtCommon i vs SchemeCall [ret, CPrimVal fc (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs i vs args) ++ ")")
  schExtCommon i vs SchemeCall [ret, fn, args, world]
       = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(schExp i vs fn) ++")) "
                    ++ !(readArgs i vs args) ++ ")")
  schExtCommon i vs PutStr [arg, world]
      = pure $ "(display " ++ !(schExp i vs arg) ++ ") " ++
            mkWorld (schConstructor (NS ["Builtin"] (UN "MkUnit")) 0 []) -- code for MkUnit
  schExtCommon i vs GetStr [world]
      = pure $ mkWorld "(blodwen-get-line (current-input-port))"
  schExtCommon i vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-open "
                                      ++ !(schExp i vs file) ++ " "
                                      ++ !(schExp i vs mode) ++ " "
                                      ++ !(schExp i vs bin) ++ ")"
  schExtCommon i vs FileClose [file, world]
      = pure $ "(blodwen-close-port " ++ !(schExp i vs file) ++ ") " ++
            mkWorld (schConstructor (NS ["Builtin"] (UN "MkUnit")) 0 [])
  schExtCommon i vs FileReadLine [file, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-get-line " ++ !(schExp i vs file) ++ ")"
  schExtCommon i vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-putstring "
                                        ++ !(schExp i vs file) ++ " "
                                        ++ !(schExp i vs str) ++ ")"
  schExtCommon i vs FileEOF [file, world]
      = pure $ mkWorld $ "(blodwen-eof " ++ !(schExp i vs file) ++ ")"
  schExtCommon i vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(schExp i vs ref) ++ ")"
  schExtCommon i vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! "
                           ++ !(schExp i vs ref) ++ " "
                           ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs VoidElim [_, _]
      = pure "(display \"Error: Executed 'void'\")"
  schExtCommon i vs (Unknown n) args
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon i vs Stdin [] = pure "(current-input-port)"
  schExtCommon i vs Stdout [] = pure "(current-output-port)"
  schExtCommon i vs Stderr [] = pure "(current-error-port)"
  schExtCommon i vs prim args
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  schDef : {auto c : Ref Ctxt Defs} ->
           {auto assembler: Assembler} ->
           Name -> CDef -> Core String
  schDef n (MkFun args exp) =
    let vs = initJvars args
        nArgs = cast {to=Int} $ length args
    in pure $ createMethod (jvmName !(getFullName n)) (length args) !(schExp nArgs vs exp)
  schDef n (MkError exp) =
    pure $ createMethod (jvmName !(getFullName n)) 0 !(schExp 0 [] exp)
  schDef n (MkForeign _ _ _) = pure "" -- compiled by specific back end
  schDef n (MkCon t a) = pure "" -- Nothing to compile here

-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getJvmBytecode : {auto c : Ref Ctxt Defs} ->
            Assembler ->
            (schExtPrim : {vars : _} -> Int -> Jvars vars -> ExtPrim -> List (CExp vars) -> Core String) ->
            (schString : String -> String) ->
            Defs -> Name -> Core String
getJvmBytecode assembler schExtPrim schString defs n
    = case !(lookupCtxtExact n (gamma defs)) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => schDef schExtPrim schString n d
