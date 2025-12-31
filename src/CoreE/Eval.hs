{-# LANGUAGE LambdaCase #-}

module CoreE.Eval where

import Syntax
import Utils (arithOp, compareOp)

lookupv :: Value -> Integer -> Maybe Value
lookupv (VMrg _ v2) 0 = Just v2
lookupv (VMrg v1 _) n = lookupv v1 (n - 1)
lookupv _ _ = Nothing

rlookupv :: Value -> String -> Maybe Value
rlookupv (VRcd l v) label
    | l == label = Just v
rlookupv (VMrg v1 v2) label =
    case (rlookupv v1 label, rlookupv v2 label) of
        (Just vL, Nothing) -> Just vL
        (Nothing, Just vR) -> Just vR
        (_, _) -> Nothing
rlookupv _ _ = Nothing

getCase :: String -> [(Pattern, CoreTm)] -> Maybe CoreTm
getCase _ [] = Nothing
getCase l (((l', _), tm) : xs) =
    if l == l' then Just tm else getCase l xs

eval :: Value -> CoreTm -> Maybe Value
eval env Ctx = Just env
eval _ Unit = Just VUnit
eval _ (Lit n) = Just (VInt n)
eval _ (EBool b) = VBool <$> Just b
eval _ (EString s) = VString <$> Just s
eval env (Lam t e) = Just (VClos env (Lam t e))
eval env (Proj e n) = eval env e >>= \v1 -> lookupv v1 n
eval env (Clos e1 e2) = eval env e1 >>= \v1 -> return $ VClos v1 e2
eval env (Rec s e) = eval env e >>= \v -> return $ VRcd s v
eval env (RProj e s) = eval env e >>= \v1 -> rlookupv v1 s
eval env (App e1 e2) =
    eval env e1 >>= \case
        (VClos v (Lam _ e)) ->
            eval env e2 >>= \v2 -> eval (VMrg v v2) e
        (VClos v (Fix t (Lam t' e'))) ->
            eval env e2 >>= \v2 ->
                eval (VMrg (VMrg v (VClos v (Fix t (Lam t' e')))) v2) e'
        _ -> Nothing
eval env (Mrg e1 e2) = eval env e1 >>= \v1 -> eval (VMrg env v1) e2 >>= \v2 -> return $ VMrg v1 v2
eval env (Box e1 e2) = eval env e1 >>= \v1 -> eval v1 e2
eval env (If cond e1 e2) =
    eval env cond
        >>= \case
            VBool True -> eval env e1
            VBool False -> eval env e2
            _ -> Nothing
eval env (Fix ty e) = Just (VClos env (Fix ty e))
eval env (Tag tm ty) =
    eval env tm
        >>= \v -> return $ VTag v ty
eval env (Case tm cases) =
    eval env tm
        >>= \case
            (VTag (VRcd l v) _) ->
                case getCase l cases of
                    Just tm' -> eval (mergeEnvTuple env v) tm'
                    Nothing -> Nothing
              where
                mergeEnvTuple env' v' =
                    case v' of
                        VMrg v1 v2 -> VMrg (mergeEnvTuple env' v1) v2
                        _ -> VMrg env' v'
            _ -> Nothing
eval env (BinOp (Arith op) e1 e2) =
    eval env e1
        >>= \case
            (VInt v1) ->
                eval env e2
                    >>= \case
                        (VInt v2) ->
                            VInt <$> arithOp op v1 v2
                        _ -> Nothing
            _ -> Nothing
eval env (BinOp (Comp op) e1 e2) =
    eval env e1
        >>= \v1 ->
            eval env e2
                >>= \v2 -> return $ VBool (compareOp op v1 v2)
eval env (BinOp (Logic op) e1 e2) =
    eval env e1
        >>= \case
            (VBool b1) ->
                eval env e2
                    >>= \case
                        (VBool b2) ->
                            case op of
                                And -> return $ VBool (b1 && b2)
                                Or -> return $ VBool (b1 || b2)
                        _ -> Nothing
            _ -> Nothing
eval env (UnOp Not e1) = case eval env e1 of
    Just (VBool b) -> Just (VBool (not b))
    _ -> Nothing
eval env (Nil ty) = Just (VNil ty)
eval env (Cons e1 e2) =
    eval env e1 >>= \v1 ->
        eval env e2 >>= \v2 ->
            return $ VCons v1 v2
eval env (LCase e1 e2 e3) = case eval env e1 of
    Just (VNil ty) -> eval env e2
    Just (VCons v1 v2) -> eval (VMrg (VMrg env v1) v2) e3
    _ -> Nothing
eval _ (CLam _ _) = Nothing
eval env (Anno tm _) = eval env tm
