{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use >=>" #-}

module Source.Elaboration where

import Source.Errors
import Syntax

elaborateTyp :: SourceTyp -> CoreTyp
elaborateTyp TySUnit = TyCUnit
elaborateTyp TySInt = TyCInt
elaborateTyp TySBool = TyCBool
elaborateTyp TySString = TyCString
elaborateTyp (TySRecord label ty) = TyCRecord label (elaborateTyp ty)
elaborateTyp (TySAnd ty1 ty2) = TyCAnd (elaborateTyp ty1) (elaborateTyp ty2)
elaborateTyp (TySArrow ty1 ty2) = TyCArrow (elaborateTyp ty1) (elaborateTyp ty2)

type Elab       = (SourceTyp, CoreTm)
type Context    = SourceTyp
type Message    = String
type Suggestion = String

generateError :: Message -> Either SourceTypeError Elab
generateError msg = Left $ STypeError msg

-- Lookup based on indexing
lookupt :: SourceTyp -> Integer -> Maybe SourceTyp
lookupt (TySAnd _ tB) 0 = Just tB
lookupt (TySAnd tA _) n = lookupt tA (n - 1)
lookupt _ _ = Nothing

containment :: SourceTyp -> SourceTyp -> Bool
containment (TySRecord l tA) (TySRecord label typ) =
    l == label && tA == typ
containment (TySRecord l tA) (TySAnd tB tC) =
    (containment (TySRecord l tA) tB && not (isLabel l tC))
        || (containment (TySRecord l tA) tC && not (isLabel l tB))
    where   isLabel :: String -> SourceTyp -> Bool
            isLabel l' (TySRecord label _)  =
                l' == label
            isLabel l' (TySAnd ty1 ty2)     =
                isLabel l' ty1 || isLabel l' ty2
            isLabel _ _                     = False
containment _ _ = False

rlookupt :: SourceTyp -> String -> Maybe SourceTyp
rlookupt (TySRecord l t) label
    | l == label = Just t
rlookupt (TySAnd tA tB) label =
    case rlookupt tB label of
        Just t -> Just t
        Nothing -> rlookupt tA label
rlookupt _ _ = Nothing

countTypesInConstructor :: SourceTyp -> Either SourceTypeError Int
countTypesInConstructor (TySAnd tA _) =
    countTypesInConstructor tA >>= \left -> return $ left + 1
countTypesInConstructor _ =
    Right 1

elaborateInfer  :: SourceTyp 
                -> SourceTm 
                -> Either SourceTypeError Elab
elaborateInfer ctx TmCtx                            = pure (ctx, Ctx)
elaborateInfer _ TmUnit                             = pure (TySUnit, Unit)
elaborateInfer _ (TmLit i)                          = pure (TySInt, Lit i)
elaborateInfer _ (TmBool b)                         = pure (TySBool, EBool b)
elaborateInfer _ (TmString s)                       = pure (TySString, EString s)
elaborateInfer ctx (TmLam tA tm)                    = do
    (tB, tm') <- elaborateInfer (TySAnd ctx tA) tm
    return (TySArrow tA tB, Lam (elaborateTyp tA) tm')
elaborateInfer _ (TmClos e1 tA e2)                  = do
    (gamma', e1')   <- elaborateInfer TySUnit e1
    (tB, e2')       <- elaborateInfer (TySAnd gamma' tA) e2
    return (TySArrow tA tB, Box e1' (Lam (elaborateTyp tA) e2'))
elaborateInfer ctx (TmRec l tm)                     = do
    (tA, tm') <- elaborateInfer ctx tm
    return (TySRecord l tA, Rec l tm')
elaborateInfer ctx (TmRProj tm l)                   = do
    (tB, tm') <- elaborateInfer ctx tm
    case rlookupt tB l of
        Just tA -> if containment (TySRecord l tA) tB
            then Right (tA, RProj tm' l)
            else generateError (show ctx ++ "\n Containment failed for labeled lookup.\n Term: " ++ show tm)
        Nothing -> generateError ("Check whether label " ++ show l ++ " exists in the record.\n Term" ++ show tm)
elaborateInfer ctx (TmProj tm n)                    = do
    (tB, tm') <- elaborateInfer ctx tm
    case lookupt tB n of
        Just tA -> Right (tA, Proj tm' n)
        Nothing -> generateError ("Type error on index lookup failed.\n Term" ++ show tm')
elaborateInfer ctx (TmApp tm1 tm2)                  = do
    (typ, tm1') <- elaborateInfer ctx tm1
    case typ of
        (TySArrow tA tB) -> do
            tm2' <- elaborateCheck ctx tm2 tA
            return (tB, App tm1' tm2')
        _ -> generateError ("Type error on application: function type expected, but got" ++ show typ)
elaborateInfer ctx (TmMrg tm1 tm2)                  = do
    (ty1, tm1') <- elaborateInfer ctx tm1
    (ty2, tm2') <- elaborateInfer (TySAnd ctx ty1) tm2 
    return (TySAnd ty1 ty2, Mrg tm1' tm2')
elaborateInfer ctx (TmBox tm1 tm2)                  = do
    (ctx', tm1')    <- elaborateInfer ctx tm1
    (ty, tm2')      <- elaborateInfer ctx' tm2
    return (ty, Box tm1' tm2')
elaborateInfer ctx (TmIf tm1 tm2 tm3)               = do
    tm1'        <- elaborateCheck ctx tm1 TySBool
    (ty2, tm2') <- elaborateInfer ctx tm2
    tm3'        <- elaborateCheck ctx tm3 ty2
    return (ty2, If tm1' tm2' tm3')
elaborateInfer ctx (TmBinOp (Arith op) tm1 tm2)     = do
    tm1' <- elaborateCheck ctx tm1 TySInt
    tm2' <- elaborateCheck ctx tm2 TySInt
    return (TySInt, BinOp (Arith op) tm1' tm2')
elaborateInfer ctx (TmBinOp (Comp op) tm1 tm2)      = do
    (ty, tm1') <- elaborateInfer ctx tm1
    if ty `elem` [TySInt, TySBool, TySString]
    then do tm2' <- elaborateCheck ctx tm2 ty
            return (TySBool, BinOp (Comp op) tm1' tm2')
    else generateError ("Type error on comparsion operation `" ++ show op ++ "`. Types on both sides must be String.")
elaborateInfer ctx (TmBinOp (Logic op) tm1 tm2)     = do
    tm1' <- elaborateCheck ctx tm1 TySBool
    tm2' <- elaborateCheck ctx tm2 TySBool
    return (TySBool, BinOp (Logic op) tm1' tm2')
elaborateInfer ctx (TmUnOp Not tm) =
    case elaborateInfer ctx tm of
        Right (ty, tm') -> Right (ty, UnOp Not tm')
        Left err -> Left err

elaborateCheck :: SourceTyp -> SourceTm -> SourceTyp -> Either SourceTypeError CoreTm
elaborateCheck ctx tm typ = do
    (ty', e') <- elaborateInfer ctx tm 
    if typ == ty'
    then Right e'
    else Left $ STypeError ("Couldn't match expected type \'" ++ show typ ++ "\' with actual type \'" ++ show ty' ++ "\'")
