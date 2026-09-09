-- | Evaluation of the nameless core: a transcription of the big-step semantics
--   @big@ of the Rocq mechanization (FirstForall/Rocq/exists/Conserve.v), which is
--   proved equivalent to the small-step semantics of Semantics.v. The runtime
--   environment is a value environment, i.e. a @Unit@ / @Merge@ / @TMerge@ chain.
module CoreFE.Eval where

import CoreFE.Syntax
    ( TyEnvE(TypeEq),
      Exp(..),
      Typ(TyBoxT),
      Literal(LitBool, LitInt),
      BinOp(EqEq, Add, Sub, Mul, LessThan),
      TyEnv )

-- | @lookupv@: the @n@-th term entry of a value environment.
lookupv :: Exp -> Int -> Maybe Exp
lookupv (Merge _ v) 0 = pure v
lookupv (Merge ve _) n = lookupv ve (n - 1)
lookupv (TMerge ve _) n = lookupv ve n
lookupv _ _ = Nothing

-- | @c2g@ (written @|δ|@ in the paper): the type entries of a value environment,
--   as a concrete context.
c2g :: Exp -> TyEnv
c2g (Merge e1 _) = c2g e1
c2g (TMerge e1 b) = TypeEq b : c2g e1
c2g _ = []

-- | @big_box@: close a type definition over the current context, unless it is a
--   box already.
wrapEnvInTyBox :: TyEnv -> Typ -> Typ
wrapEnvInTyBox _ t@(TyBoxT _ _) = t
wrapEnvInTyBox env t = TyBoxT env t

-- | @rlookupv@: label selection on a value environment. Searches the last entry
--   when it is a record or a nested environment, and skips type entries.
rlookupv :: Exp -> String -> Maybe Exp
rlookupv (Merge d (Rec l1 v)) l
  | l == l1 = pure v                                  -- rvlzero
  | otherwise = rlookupv d l                          -- rvl_left
rlookupv (Merge _ d1@(Merge _ _)) l = rlookupv d1 l   -- rvl_right
rlookupv (Merge _ d1@(TMerge _ _)) l = rlookupv d1 l  -- rvl_right
rlookupv (TMerge d _) l = rlookupv d l                -- rvl_left_t
rlookupv _ _ = Nothing

-- | @econcat@ (written @δ + δ1@ in the paper): append the entries of the second
--   environment to the first.
econcat :: Exp -> Exp -> Exp
econcat e1 (Merge e3 e4) =
  case e3 of
    Merge _ _  -> Merge (econcat e1 e3) e4
    TMerge _ _ -> Merge (econcat e1 e3) e4
    _          -> Merge e1 e4
econcat e1 (TMerge e3 a) =
  case e3 of
    Merge _ _  -> TMerge (econcat e1 e3) a
    TMerge _ _ -> TMerge (econcat e1 e3) a
    _          -> TMerge e1 a
econcat e1 _ = e1

-- | @big ve e v@.
eval :: Exp -> Exp -> Maybe Exp
eval env = go
  where
    go (Lit n) = pure $ Lit n                                    -- b_lit
    go (Var n) = lookupv env n                                   -- b_var
    go (Lam e) = pure $ Clos env e                               -- b_lam
    go e@(Clos _ _) = pure e                                     -- b_clos
    go (App e1 e2) = do                                          -- b_beta
      Clos env' e <- go e1
      v2 <- go e2
      eval (Merge env' v2) e
    go (TLam e) = pure $ TClos env e                             -- b_blam
    go e@(TClos _ _) = pure e                                    -- b_bclos
    go (TApp e a) = do                                           -- b_tbeta
      TClos env' e1 <- go e
      eval (TMerge env' (TyBoxT (c2g env) a)) e1
    go (Box e1 e2) = do                                          -- b_box
      v1 <- go e1
      eval v1 e2
    go Unit = pure Unit                                          -- b_nil
    go (Merge e1 e2) = do                                        -- b_edef
      ve1 <- go e1
      v2 <- eval (econcat env ve1) e2
      pure $ Merge ve1 v2
    go (TMerge e1 a) = do                                        -- b_tdef
      ve1 <- go e1
      pure $ TMerge ve1 (wrapEnvInTyBox (c2g (econcat env ve1)) a)
    go (Rec l e) = Rec l <$> go e                                -- b_rec
    go (RProj e l) = do                                          -- b_proj
      v <- go e
      rlookupv v l
    go (Anno e _) = go e
    go (BinOp (Add e1 e2)) = do
        Lit (LitInt v1) <- go e1
        Lit (LitInt v2) <- go e2
        pure $ Lit (LitInt (v1 + v2))
    go (BinOp (Sub e1 e2)) = do
        Lit (LitInt v1) <- go e1
        Lit (LitInt v2) <- go e2
        pure $ Lit (LitInt (v1 - v2))
    go (BinOp (Mul e1 e2)) = do
        Lit (LitInt v1) <- go e1
        Lit (LitInt v2) <- go e2
        pure $ Lit (LitInt (v1 * v2))
    go (BinOp (EqEq e1 e2)) = do
        v1 <- go e1
        v2 <- go e2
        pure $ Lit (LitBool (v1 == v2))
    go (BinOp (LessThan e1 e2)) = do
        Lit (LitInt v1) <- go e1
        Lit (LitInt v2) <- go e2
        pure $ Lit (LitBool (v1 < v2))
    go (EList es) = do
        vs <- mapM go es
        pure $ EList vs
    go (ETake n e) = do
        EList vs <- go e
        pure $ EList (take n vs)
    go (ELength e) = do
        EList vs <- go e
        pure $ Lit (LitInt (length vs))
