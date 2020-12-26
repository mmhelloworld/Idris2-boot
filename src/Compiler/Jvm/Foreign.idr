module Compiler.Jvm.Foreign

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

%access public export

namespace ForeignType
    data ForeignType
        = AtomicForeignType InferredType
        | FunctionForeignType
            String -- (interfaceName: String)
            String -- (methodName: String)
            InferredFunctionType -- (interfaceMethodType: InferredFunctionType)
            InferredFunctionType -- (implementationMethodType: InferredFunctionType)

    getInferredType : ForeignType -> InferredType
    getInferredType (FunctionForeignType interfaceName _ _ _) = IRef interfaceName
    getInferredType (AtomicForeignType ty) = ty

namespace ForeignImplementationType
    data ForeignImplementationType
        = AtomicForeignImplementationType InferredType
        | FunctionForeignImplementationType InferredFunctionType

    getInferredType : FC -> ForeignImplementationType -> Asm InferredType
    getInferredType fc (AtomicForeignImplementationType ty) = Pure ty
    getInferredType fc _ = Throw fc "Callback functions cannot be higher order"

    mutual
        parseCallbackType : FC -> List CFType -> CFType -> Asm ForeignImplementationType
        parseCallbackType fc arguments (CFFun CFWorld returnType) = parseCallbackType fc arguments returnType
        parseCallbackType fc arguments (CFFun nextArgument returnType) =
            parseCallbackType fc (nextArgument :: arguments) returnType
        parseCallbackType fc arguments returnType = do
                argumentForeignTypes <- traverse parseInferredType (reverse arguments)
                returnForeignType <- parseInferredType returnType
                Pure $ FunctionForeignImplementationType (MkInferredFunctionType returnForeignType argumentForeignTypes)
            where
                parseInferredType : CFType -> Asm InferredType
                parseInferredType ty = do
                    foreignType <- parse fc ty
                    inferredType <- getInferredType fc foreignType
                    Pure inferredType

        parse : FC -> CFType -> Asm ForeignImplementationType
        parse _ CFUnit = Pure $ AtomicForeignImplementationType IVoid
        parse _ CFInt = Pure $ AtomicForeignImplementationType IInt
        parse _ CFString = Pure $ AtomicForeignImplementationType inferredStringType
        parse _ CFDouble = Pure $ AtomicForeignImplementationType IDouble
        parse _ CFChar = Pure $ AtomicForeignImplementationType IChar
        parse _ CFWorld = Pure $ AtomicForeignImplementationType IInt
        parse fc (CFIORes returnType) = parse fc returnType
        parse fc (CFFun argument returnType) = parseCallbackType fc [argument] returnType
        parse _ _ = Pure $ AtomicForeignImplementationType inferredObjectType

throwExplicitFunctionDescriptorRequired : FC -> Asm a
throwExplicitFunctionDescriptorRequired fc = Throw fc ("Explicit function descriptor must be provided while " ++
                                                        "passing idris functions to JVM functions")

parseForeignCallbackDeclarationType : FC -> (descriptorParts : List String) -> Asm InferredFunctionType
parseForeignCallbackDeclarationType fc [] = throwExplicitFunctionDescriptorRequired fc
parseForeignCallbackDeclarationType _ [returnDescriptor] = Pure $ MkInferredFunctionType (parse returnDescriptor) []
parseForeignCallbackDeclarationType _ (arg :: next) =
    let (argumentTypesReversed, returnType) = go [] arg next
    in Pure $ MkInferredFunctionType returnType (reverse argumentTypesReversed)
  where
    go : List InferredType -> String -> List String -> (List InferredType, InferredType)
    go acc descriptor (nextArgument :: rest) = go (parse descriptor :: acc) nextArgument rest
    go acc descriptor [] = (acc, parse descriptor)

getForeignCallbackDeclarationType : FC -> ForeignImplementationType -> Asm ForeignType
getForeignCallbackDeclarationType fc (AtomicForeignImplementationType ty) = Pure $ AtomicForeignType ty
getForeignCallbackDeclarationType fc _ = throwExplicitFunctionDescriptorRequired fc
{-
 - Callbacks are represented as JVM functional interface types. For example, a foreign descriptor
 - might have a callback like "jvm:foo:String java/util/function/ToIntFunction#applyAsInt#Object#Int Int".
 - This descriptor provides the underlying functional interface method type for the second argument with the
 - interface name, interface abstract method name, input and output types, all separated by "#".
 -}
parseForeignType : FC -> String -> ForeignImplementationType -> Asm ForeignType
parseForeignType fc descriptor implementationType = case Strings.split (== '#') descriptor of
    (interfaceName :: interfaceMethodName :: signatureParts) =>
        case implementationType of
            AtomicForeignImplementationType _ => Throw fc ("Cannot pass non function argument as a JVM function")
            FunctionForeignImplementationType implementationType => do
                declarationType <- parseForeignCallbackDeclarationType fc signatureParts
                Pure $ FunctionForeignType interfaceName interfaceMethodName declarationType implementationType
    [_] => case implementationType of
        FunctionForeignImplementationType _ => throwExplicitFunctionDescriptorRequired fc
        _ => Pure $ AtomicForeignType $ parse descriptor

parseForeignFunctionDescriptor : FC -> List String -> List ForeignImplementationType ->
    InferredType -> Asm (String, String, InferredType, List ForeignType)
parseForeignFunctionDescriptor fc (functionDescriptor :: className :: _) argumentTypes returnType =
    case Strings.break (== '(') functionDescriptor of
        (fn, "") => do
            argumentDeclarationTypes <- traverse (getForeignCallbackDeclarationType fc) argumentTypes
            Pure (className, fn, returnType, argumentDeclarationTypes)
        (fn, signature) => do
            let descriptorsWithIdrisTypes = List.zip (Strings.split (== ' ') (strTail signature)) argumentTypes
            (argumentTypesReversed, returnType) <- go [] descriptorsWithIdrisTypes
            Pure (className, fn, returnType, reverse argumentTypesReversed)
  where
    go : List ForeignType -> List (String, ForeignImplementationType) -> Asm (List ForeignType, InferredType)
    go acc ((returnTypeDesc, _) :: []) = Pure (acc, parse returnTypeDesc)
    go acc ((argument, ty) :: rest) = do
        foreignType <- parseForeignType fc argument ty
        go (foreignType :: acc) rest
parseForeignFunctionDescriptor fc descriptors _ _ = Throw fc $ "Invalid foreign descriptor: " ++ show descriptors

findJvmDescriptor : FC -> List String -> Asm (List String)
findJvmDescriptor fc [] = Throw fc "Cannot compile foreign function to JVM as JVM foreign descriptor is missing"
findJvmDescriptor fc (descriptor :: descriptors) = case parseCC descriptor of
    Just ("jvm", descriptorParts) => Pure descriptorParts
    _ => findJvmDescriptor fc descriptors

getArgumentIndices : Nat -> List String -> SortedMap String Nat
getArgumentIndices Z _ = SortedMap.empty
getArgumentIndices (S lastArgIndex) args = SortedMap.fromList $ List.zip args [0 .. lastArgIndex]

getPrimMethodName : String -> String
getPrimMethodName name =
    if strHead name == '.' then "prim__jvmInstance"
    else "prim__jvmStatic"

inferForeign : Name -> FC -> List String -> List CFType -> CFType -> Asm ()
inferForeign idrisName fc foreignDescriptors argumentTypes returnType = do
    resetScope
    let jname = jvmName idrisName
    let fileName = file fc
    let jvmClassAndMethodName = getIdrisFunctionName (className jname) fileName (methodName jname)
    jvmArgumentTypes <- traverse (parse fc) argumentTypes
    jvmDescriptor <- findJvmDescriptor fc foreignDescriptors
    jvmReturnType <- getInferredType fc !(parse fc returnType)
    (foreignFunctionClassName, foreignFunctionName, jvmReturnType, jvmArgumentTypes) <-
        parseForeignFunctionDescriptor fc jvmDescriptor jvmArgumentTypes jvmReturnType
    let jvmArgumentTypes = getInferredType <$> jvmArgumentTypes
    let inferredFunctionType = MkInferredFunctionType jvmReturnType jvmArgumentTypes
    scopeIndex <- newScopeIndex
    let arity = length jvmArgumentTypes
    let argumentNames =
       if arity > 0 then (\argumentIndex => "arg" ++ show argumentIndex) <$> [0 .. Nat.pred arity] else []
    let argIndices = getArgumentIndices arity argumentNames
    let argumentTypesByName = SortedMap.fromList $ List.zip argumentNames jvmArgumentTypes
    let tailCallCategory = MkTailCallCategory False False
    let function = MkFunction jname inferredFunctionType SortedMap.empty 0 jvmClassAndMethodName
        tailCallCategory
        (NmExtPrim fc (NS [] $ UN $ getPrimMethodName foreignFunctionName) [
            NmCon fc (UN $ createExtPrimTypeSpec jvmReturnType) Nothing [],
            NmPrimVal fc (Str $ foreignFunctionClassName ++ "." ++ foreignFunctionName),
            getJvmExtPrimArguments $ List.zip argumentTypes $ SortedMap.toList argumentTypesByName,
            NmPrimVal fc WorldVal])
    setCurrentFunction function
    updateState $ record { functions $= SortedMap.insert jname function }
    let functionScope = MkScope scopeIndex Nothing argumentTypesByName argIndices jvmReturnType arity
                            (0, 0) ("", "") []
    updateScope scopeIndex functionScope
  where
    getJvmExtPrimArguments : List (CFType, String, InferredType) -> NamedCExp
    getJvmExtPrimArguments [] = NmCon fc (UN "emptyForeignArg") (Just 0) []
    getJvmExtPrimArguments ((CFWorld, _, _) :: rest) = getJvmExtPrimArguments rest
    getJvmExtPrimArguments ((_, name, ty) :: rest) = NmCon fc (UN "foreignArg") (Just 1) [
        NmCon fc (UN $ createExtPrimTypeSpec ty) (Just 0) [],
        NmLocal fc (UN name),
        getJvmExtPrimArguments rest ]