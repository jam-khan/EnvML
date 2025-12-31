{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}
module EnvML.LocallyNameless where

import EnvML.Errors
import Syntax

type Depth = Integer

{- | `debruijnIndex stack var i` finds the De Bruijn index of `var` in `stack` starting at index `i`.
  Returns `Just index` or `Nothing` if not found.

=== Example:
>>> debruijnIndex [("x", STInt), ("y", STBool)] "x"
Just 1
-}
debruijnIndex :: Params -> String -> Maybe Integer
debruijnIndex stack l = findDebruijnIndex (reverse stack) l 0

{- | `findDebruijnIndex stack var l i` finds the De Bruijn in the stack by matching the first identifier found.
 Returns `Just index` or `Nothing` if not found.

=== Example:
>>> findDebruijnIndex [("x", STInt)] "x" 0
Just 0
>>> findDebruijnIndex [ ] "x" 0
Nothing
-}
findDebruijnIndex :: Params -> String -> Depth -> Maybe Integer
findDebruijnIndex [] _ _ = Nothing
findDebruijnIndex ((x, _) : xs) l i =
    if l == x then Just i else findDebruijnIndex xs l (i + 1)

{- | Converts an AST to a locally nameless representation.

This function replaces variable names with De Bruijn indices.

Returns:
`Right SurfaceTm`: The AST with variables removed.
`Left LocallyNamelessError`: An error if the conversion fails.

=== Example:
>>> astToLocallyNameless [("x", STInt)] (SVar "x")
Right (SProj SCtx 0)

>>> astToLocallyNameless [("x", STInt)] (SVar "y")
Right (SRProj SCtx "y")

>>> astToLocallyNameless [] (SLam [("x", STInt), ("y", STInt)] (SBinOp (Arith Add) (SVar "x") (SVar "y")))
Right (SLam [("x",STInt),("y",STInt)] (SBinOp (Arith Add) (SProj SCtx 1) (SProj SCtx 0)))
-}
astToLocallyNameless :: Params -> SurfaceTm -> Either LocallyNamelessError SurfaceTm
astToLocallyNameless _ SCtx = Right SCtx
astToLocallyNameless _ SUnit = Right SUnit
astToLocallyNameless _ (SLit i) = Right (SLit i)
astToLocallyNameless _ (SBool b) = Right (SBool b)
astToLocallyNameless _ (SString s) = Right (SString s)
astToLocallyNameless stack (SLam params tm) =
    SLam
        <$> Right params
        <*> astToLocallyNameless (stack ++ params) tm
astToLocallyNameless stack (SClos tm1 params tm2) =
    SClos
        <$> astToLocallyNameless params tm1
        <*> Right params
        <*> astToLocallyNameless (stack ++ params) tm2
astToLocallyNameless stack (SRec l tm) =
    SRec l <$> astToLocallyNameless stack tm
astToLocallyNameless stack (SRProj tm l) =
    SRProj <$> astToLocallyNameless stack tm <*> Right l
astToLocallyNameless stack (SProj tm i) =
    SProj <$> astToLocallyNameless stack tm <*> Right i
astToLocallyNameless stack (SApp tm1 terms) =
    SApp
        <$> astToLocallyNameless stack tm1
        <*> processMultipleTerms stack terms
astToLocallyNameless stack (SMrg tm1 tm2) =
    SMrg
        <$> astToLocallyNameless stack tm1
        <*> astToLocallyNameless
            (stack ++ [("?", STUnit)])
            tm2
astToLocallyNameless stack (SBox tm1 tm2) =
    SBox
        <$> astToLocallyNameless stack tm1
        <*> astToLocallyNameless stack tm2
astToLocallyNameless stack (SVar var) =
    case debruijnIndex stack var of
        Just i -> Right (SProj SCtx i)
        Nothing -> Right (SRProj SCtx var)
astToLocallyNameless _ (SStruct params tm) =
    SStruct params
        <$> astToLocallyNameless params tm -- Modules are encapsulated and hence, scope is empty except arguments
astToLocallyNameless stack (SFunc name params typ tm) =
    SFunc name params typ
        <$> astToLocallyNameless (stack ++ [(name, STUnit)] ++ params) tm
astToLocallyNameless _ (SModule name params tm) =
    SModule name params <$> astToLocallyNameless params tm
astToLocallyNameless stack (SLet args tm) =
    do
        processedLet <- processLet (SLet args tm)
        case processedLet of
            (SLet [(x1, ty1, tm1)] tm2) ->
                do
                    tm1' <- astToLocallyNameless stack tm1
                    SLet [(x1, ty1, tm1')] <$> astToLocallyNameless (stack ++ [(x1, ty1)]) tm2
            _ ->
                Left $
                    LocallyNamelessFailed
                        "Got unexpected response from internal utility function `processLet`"
astToLocallyNameless stack (SLetrec args tm) =
    do
        processedLet <- processLet (SLetrec args tm)
        case processedLet of
            (SLetrec [(x1, ty1, tm1)] tm2) ->
                do
                    tm1' <- case tm1 of
                        SLam _ _ -> astToLocallyNameless (stack ++ [(x1, ty1)]) tm1
                        _ -> astToLocallyNameless stack tm1
                    SLetrec [(x1, ty1, tm1')] <$> astToLocallyNameless (stack ++ [(x1, ty1)]) tm2
            _ ->
                Left $
                    LocallyNamelessFailed
                        "Got unexpected response from internal utility function `processLet`"
astToLocallyNameless stack (SADTInst (l, terms) typ) =
    do
        terms' <- processMultipleTerms stack terms
        return $ SADTInst (l, terms') typ
astToLocallyNameless stack (SCase tm cases) =
    do
        tm' <- astToLocallyNameless stack tm
        cases' <- processCases stack cases
        return $ SCase tm' cases'
astToLocallyNameless stack (SBinOp op tm1 tm2) =
    SBinOp op
        <$> astToLocallyNameless stack tm1
        <*> astToLocallyNameless stack tm2
astToLocallyNameless stack (SUnOp op tm) =
    SUnOp op
        <$> astToLocallyNameless stack tm
astToLocallyNameless stack (SIf tm1 tm2 tm3) =
    SIf
        <$> astToLocallyNameless stack tm1
        <*> astToLocallyNameless stack tm2
        <*> astToLocallyNameless stack tm3
astToLocallyNameless _ (SAliasTyp l ty) =
    Left $
        LocallyNamelessFailed
            ("Type alias not resolved: type " ++ l ++ " = " ++ show ty)
astToLocallyNameless _stack tm =
    Left $
        LocallyNamelessFailed
            ("Function not fully implemented." ++ show tm)

processCases :: Params -> Cases -> Either LocallyNamelessError Cases
processCases _ [] = Right []
processCases stack (((constructor, bindings), term) : rest) =
    do
        rest' <- processCases stack rest
        term' <- astToLocallyNameless (stack ++ map (\b -> (b, STUnit)) bindings) term
        return $ ((constructor, bindings), term') : rest'

processLet :: SurfaceTm -> Either LocallyNamelessError SurfaceTm
processLet (SLet [x] tm) = Right $ SLet [x] tm
processLet (SLet (x : xs) tm) = SLet [x] <$> processLet (SLet xs tm)
processLet (SLetrec [x] tm) = Right $ SLetrec [x] tm
processLet (SLetrec (x : xs) tm) = SLetrec [x] <$> processLet (SLetrec xs tm)
processLet _ = Left $ LocallyNamelessFailed "Either a let with no params or Let utility function called on wrong term."

-- | Helper for `astToLocallyNameless`
processMultipleTerms :: Params -> [SurfaceTm] -> Either LocallyNamelessError [SurfaceTm]
processMultipleTerms _params [] = Right []
processMultipleTerms params (x : xs) =
    astToLocallyNameless params x >>= \x' ->
        processMultipleTerms params xs >>= \xs' -> Right (x' : xs')

-- | Helper for `astToLocallyNameless`
processLetArguments :: [(String, SurfaceTyp, SurfaceTm)] -> [(String, SurfaceTyp)]
processLetArguments [] = []
processLetArguments ((x, ty, _) : xs) =
    (x, ty) : processLetArguments xs
