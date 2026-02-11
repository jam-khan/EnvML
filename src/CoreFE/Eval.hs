module CoreFE.Eval where

import CoreFE.Syntax

lookupv :: Env -> Int -> Maybe Exp
lookupv [] _ = Nothing
lookupv (ExpE v : _) 0 = pure v
lookupv (ExpE _ : xs) n = lookupv xs (n - 1)
lookupv (TypE _ : xs) n = lookupv xs n

c2g :: Env -> TyEnv
c2g env = [TypeEq a | TypE a <- env]

wrapEnvInTyBox :: TyEnv -> Typ -> Typ
wrapEnvInTyBox _ t@(TyBoxT _ _) = t
wrapEnvInTyBox env t = TyBoxT env t

-- Record lookup
rlookupv :: Exp -> String -> Maybe Exp
rlookupv (FEnv (ExpE (Rec l1 v) : d)) l
  | l == l1 = pure v
  | l /= l1 = rlookupv (FEnv d) l
rlookupv (FEnv (ExpE (FEnv d1) : _)) l =
  rlookupv (FEnv d1) l
rlookupv (FEnv (_ : d)) l =
  rlookupv (FEnv d) l
rlookupv _ _ = Nothing

eval :: Env -> Exp -> Maybe Exp
eval env = go
  where
    go (Lit n) = pure $ Lit n
    go (Var n) = lookupv env n
    go (Lam e) = pure $ Clos env e
    go e@(Clos _ _) = pure e
    go (App e1 e2) = do
      Clos env' e <- eval env e1
      v2 <- eval env e2
      eval (ExpE v2 : env') e
    go (TLam e) = pure $ TClos env e
    go e@(TClos _ _) = pure e
    go (TApp e a) = do
      TClos env' e1 <- eval env e
      eval (TypE (TyBoxT (c2g env) a) : env') e1
    go (Box e1 e2) = do
      FEnv v <- eval env (FEnv e1)
      eval v e2
    go e@(FEnv []) = pure e
    go (FEnv (ExpE e' : ve)) = do
      FEnv ve1 <- eval env (FEnv ve)
      ee <- eval (ve1 ++ env) e'
      pure $ FEnv (ExpE ee : ve1)
    go (FEnv (TypE a : e1)) = do
      -- b_tdef
      FEnv ve1 <- eval env (FEnv e1)
      let b = TyBoxT (c2g (ve1 ++ env)) a
      return $ FEnv (TypE b : ve1)
    go (Rec l e) = Rec l <$> eval env e
    go (RProj e l) = do
      v <- eval env e
      rlookupv v l
    go (Anno e _) =
      eval env e
    go (Fix e) = do
        Clos env' e1 <- eval env e
        let v_fix = Clos (ExpE v_fix : env') e1
        pure v_fix
    go (If cond e1 e2) = do
        Lit (LitBool b) <- eval env cond
        eval env (if b then e1 else e2)
    go (BinOp (Add e1 e2)) = do
        Lit (LitInt v1) <- eval env e1
        Lit (LitInt v2) <- eval env e2
        pure $ Lit (LitInt (v1 + v2))
    go (BinOp (Sub e1 e2)) = do
        Lit (LitInt v1) <- eval env e1
        Lit (LitInt v2) <- eval env e2
        pure $ Lit (LitInt (v1 - v2))
    go (BinOp (Mul e1 e2)) = do
        Lit (LitInt v1) <- eval env e1
        Lit (LitInt v2) <- eval env e2
        pure $ Lit (LitInt (v1 * v2))
    go (BinOp (EqEq e1 e2)) = do
        v1 <- eval env e1
        v2 <- eval env e2
        pure $ Lit (LitBool (v1 == v2))
