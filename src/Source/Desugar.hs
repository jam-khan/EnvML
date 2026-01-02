-- Function implementations follow...
{-# LANGUAGE LambdaCase #-}

{- |
Module      : Desugar
Description : A module for desugaring surface terms into source terms.
Maintainer  : Your Name <your.email@example.com>
Stability   : Experimental
Portability : Non-portable (depends on GHC extensions)

This module provides functions to transform surface-level terms into a more abstract representation suitable for further processing. The desugaring process involves converting various syntactic constructs into simpler forms, enabling easier manipulation and evaluation.

== Functions

* 'extractLetParams'            - Extracts parameter names and types from let bindings.
* 'extractLetArgs'              - Extracts argument terms from let bindings.
* 'extractLetRecParams'         - Extracts parameters from letrec bindings.
* 'processLetRecParamsArgs'     - Processes parameters and arguments for letrec bindings.
* 'processModule'               - Processes a module structure and desugars its contents.
* 'processParams'               - Desugars a list of parameters.
* 'processApplication'          - Desugars application terms.
* 'processLambda'               - Desugars lambda abstractions.
* 'desugarParam'                - Desugars a single parameter type.
* 'desugarTyp'                  - Desugars surface types into source types.
* 'desugar'                     - Main function to desugar surface terms into source terms.

== Examples

=== Example 1: Desugaring a simple lambda expression

>>> desugar (SLam [("x", STInt)] (SProj SCtx 0))
Right (TmLam TySInt (TmProj TmCtx 0))

>>> desugar (SLet [("y", STInt, SLit 5)] (SProj SCtx 0))
Right (TmApp (TmLam TySInt (TmProj TmCtx 0)) (TmLit 5))

=== Example 3: Desugaring a module

>>> desugar (SModule "MyModule" [("param1", STInt), ("param2", STInt)] (SLit 42))
Right (TmRec "MyModule" (TmStruct (TySAnd TySInt TySInt) (TmLit 42)))

=== Example 4: Handling an unsupported term

>>> desugar (SVar "undefinedVar")
Left (DesugarFailed "Variable identifier \"undefinedVar\" couldn't get transformed.")
-}
module Source.Desugar where

import Source.Errors
import Syntax

extractLetParams :: [(String, SurfaceTyp, SurfaceTm)] -> [(String, SurfaceTyp)]
extractLetParams [] = []
extractLetParams ((x, ty, _tm) : rest) =
    (x, ty) : extractLetParams rest

extractLetArgs :: [(String, SurfaceTyp, SurfaceTm)] -> [SurfaceTm]
extractLetArgs [] = []
extractLetArgs ((_x, _ty, tm) : rest) =
    tm : extractLetArgs rest

extractLetRecParams :: [(String, SurfaceTyp, SurfaceTm)] -> [(String, SurfaceTyp)]
extractLetRecParams [] = []
extractLetRecParams ((x, ty, _tm) : rest) =
    (x, ty) : extractLetParams rest

processLetRecParamsArgs :: [(String, SurfaceTyp, SurfaceTm)] -> Either DesugarError [SourceTm]
processLetRecParamsArgs [] = Right []
processLetRecParamsArgs ((_, ty, tm) : rest) =
    do
        ty' <- desugarTyp ty
        tm' <- desugar tm
        rest' <- processLetRecParamsArgs rest
        return $ TmFix ty' tm' : rest'

processModule :: SurfaceTm -> Either DesugarError SourceTm
processModule (SStruct params tm) =
    TmStruct <$> processParams params <*> desugar tm
processModule _ =
    Left $ DesugarFailed "Utility to process modules called on a non-module"

processParams :: Params -> Either DesugarError SourceTyp
processParams [] =
    Left $ DesugarFailed "Empty Params not allowed in the module struct"
processParams [(_, ty)] =
    desugarTyp ty
processParams ((_, ty) : rest) =
    TySAnd <$> desugarTyp ty <*> processParams rest

processApplication :: SurfaceTm -> Either DesugarError SourceTm
processApplication (SApp tm1 args) =
    do
        tm1' <- desugar tm1
        args' <- mapM desugar args
        return $ foldl TmApp tm1' args'
processApplication tm =
    Left $ DesugarFailed ("Utility function called on non-application: " ++ show tm)

processLambda :: SurfaceTm -> Either DesugarError SourceTm
processLambda (SLam [] tm) = desugar tm
processLambda (SLam (arg : rest) tm) =
    TmLam <$> desugarParam arg <*> processLambda (SLam rest tm)
processLambda _ =
    Left $ DesugarFailed "Utility function `processLambda` called upon non-lambda term."

desugarParam :: (String, SurfaceTyp) -> Either DesugarError SourceTyp
desugarParam (_, ty) = desugarTyp ty

desugarTyp :: SurfaceTyp -> Either DesugarError SourceTyp
desugarTyp STUnit = Right TySUnit
desugarTyp STInt = Right TySInt
desugarTyp STBool = Right TySBool
desugarTyp STString = Right TySString
desugarTyp (STAnd ty1 ty2) =
    TySAnd <$> desugarTyp ty1 <*> desugarTyp ty2
desugarTyp (STArrow ty1 ty2) =
    TySArrow <$> desugarTyp ty1 <*> desugarTyp ty2
desugarTyp (STRecord l ty) =
    TySRecord l <$> desugarTyp ty
desugarTyp (STList ty) =
    TySList <$> desugarTyp ty
desugarTyp (STUnion ty1 ty2) =
    TySUnion <$> desugarTyp ty1 <*> desugarTyp ty2
desugarTyp (STSig ty1 ty2) =
    TySSig <$> desugarTyp ty1 <*> desugarTyp ty2
desugarTyp (STIden x) =
    Left $
        DesugarFailed
            ("Type alias not expanded correctly. Type identifier remaining: " ++ show x)

desugar :: SurfaceTm -> Either DesugarError SourceTm
desugar SCtx = Right TmCtx
desugar SUnit = Right TmUnit
desugar (SLit i) = Right (TmLit i)
desugar (SBool b) = Right (TmBool b)
desugar (SString s) = Right (TmString s)
desugar (SLam params tm) = processLambda (SLam params tm)
desugar (SClos tm1 params tm2) =
    desugar tm1 >>= \tm1' ->
        processLambda (SLam params tm2) >>= \case
            (TmLam ty tm2') -> Right $ TmClos tm1' ty tm2'
            _ -> Left $ DesugarFailed "Closure must be an abstraction. Hint: Use boxes instead"
desugar (SRec l tm) =
    TmRec l <$> desugar tm
desugar (SRProj tm l) =
    TmRProj <$> desugar tm <*> Right l
desugar (SProj tm n) =
    TmProj <$> desugar tm <*> Right n
desugar (SApp tm1 args) =
    processApplication (SApp tm1 args)
desugar (SMrg tm1 tm2) =
    TmMrg <$> desugar tm1 <*> desugar tm2
desugar (SBox tm1 tm2) =
    TmBox <$> desugar tm1 <*> desugar tm2
desugar (SVar x) =
    Left $ DesugarFailed ("Variable identifier " ++ show x ++ " couldn't get transformed.")
desugar (SStruct params tm) =
    processModule (SStruct params tm)
-- I need to extract type information from the curried lambda for fixpoint
-- How to do this?
-- 1. Desugar and then, iterate through the desugared Lambda and get all the types
-- 2. Desugar Params and get the types (This one seems a better option)
desugar (SFunc name params tyOut tm) =
    do
        tyOut' <- desugarTyp tyOut
        fixTy <- getFixpointType params tyOut'
        tm' <- desugar (SLam params tm)
        return $ TmRec name (TmFix fixTy tm')
desugar (SModule name params tm) =
    TmRec name <$> desugar (SStruct params tm)
desugar (SAliasTyp l _) =
    Left $ DesugarFailed ("Type alias" ++ show l ++ "detected at desugaring phased.")
desugar (SLet [(_, ty, tm1)] tm2) =
    do
        lambda <- TmLam <$> desugarTyp ty <*> desugar tm2
        TmApp lambda <$> desugar tm1
desugar (SLetrec [(_, ty, tm1)] tm2) =
    do
        lambda <- TmLam <$> desugarTyp ty <*> desugar tm2
        app <- case tm1 of
            (SLam _ _) -> TmFix <$> desugarTyp ty <*> desugar tm1
            _ -> desugar tm1
        return $ TmApp lambda app
desugar (SLet (x : xs) _) = Left $ DesugarFailed ("Need exactly one argument in the locally nameless representation, but found " ++ show (x : xs))
desugar (SLetrec (x : xs) _) =
    Left $ DesugarFailed ("Need exactly one argument in the locally nameless representation, but found " ++ show (x : xs))
desugar (SBinOp op tm1 tm2) =
    TmBinOp op <$> desugar tm1 <*> desugar tm2
desugar (SUnOp op tm) = TmUnOp op <$> desugar tm
desugar (SAnno tm ty) = TmAnno <$> desugar tm <*> desugarTyp ty
desugar (SIf tm1 tm2 tm3) =
    TmIf <$> desugar tm1 <*> desugar tm2 <*> desugar tm3
desugar (SADTInst (label, terms) ty) =
    do
        terms' <- desugarMultipleTerms terms
        ty' <- desugarTyp ty
        return $ TmTag (TmRec label (foldl1 TmMrg terms')) ty'
desugar (SCase tm cases) = do
    cases' <- desugarCases cases
    tm' <- desugar tm
    return $ TmCase tm' cases'

-- desugar (SADTInst (label, terms) ty)
--                         =  do
--                             terms' <- desugarMultipleTerms terms
--                             ty'    <- desugarTyp ty
--                             return $ TmTag (label, terms') ty'

desugar _sourceTerm =
    Left $ DesugarFailed "Function not implemented completely.\n"

desugarCases :: Cases -> Either DesugarError [(Pattern, SourceTm)]
desugarCases [] = Right []
desugarCases ((pattern, tm) : rest) =
    do
        tm' <- desugar tm
        rest' <- desugarCases rest
        return $ (pattern, tm') : rest'

desugarMultipleTerms :: [SurfaceTm] -> Either DesugarError [SourceTm]
desugarMultipleTerms [] = Right []
desugarMultipleTerms (x : xs) = do
    x' <- desugar x
    xs' <- desugarMultipleTerms xs
    return (x' : xs')

-- | Helper to construct fixpoint type
getFixpointType :: Params -> SourceTyp -> Either DesugarError SourceTyp
getFixpointType [] ty' = Right ty'
getFixpointType [(_, ty)] ty' = TySArrow <$> desugarTyp ty <*> Right ty'
getFixpointType ((_, ty) : rest) ty' = TySArrow <$> desugarTyp ty <*> getFixpointType rest ty'
