-- | Big-step evaluation, transcribing @big@ of mech/fe_calculus (Conserve.v),
--   which the mechanization proves equivalent to the small-step semantics. The
--   runtime environment is a value environment: a @Unit@/@Merge@/@TMerge@ chain.
module CoreFE.Eval where

import CoreFE.Syntax
    ( TyEnvE(TypeEq),
      Exp(..),
      Typ(TyBoxT),
      Literal(LitBool, LitInt),
      BinOp(EqEq, Add, Sub, Mul, LessThan),
      TyEnv )

-- | @lookupv@: the @n@-th term entry.
lookupv :: Exp -> Int -> Maybe Exp
lookupv (Merge _ v) 0 = pure v
lookupv (Merge ve _) n = lookupv ve (n - 1)
lookupv (TMerge ve _) n = lookupv ve n
lookupv _ _ = Nothing

-- | @c2g@ (the paper's @|δ|@): the type entries, as a concrete context.
c2g :: Exp -> TyEnv
c2g (Merge e1 _) = c2g e1
c2g (TMerge e1 b) = TypeEq b : c2g e1
c2g _ = []

-- | @big_box@: close a type definition over the context unless it is a box.
wrapEnvInTyBox :: TyEnv -> Typ -> Typ
wrapEnvInTyBox _ t@(TyBoxT _ _) = t
wrapEnvInTyBox env t = TyBoxT env t

-- | @rlookupv@: label selection; searches the last entry, skips type entries.
rlookupv :: Exp -> String -> Maybe Exp
rlookupv (Merge d (Rec l1 v)) l                       -- rvlzero / rvl_left
  | l == l1 = pure v
  | otherwise = rlookupv d l
rlookupv (Merge _ d1@(Merge _ _)) l = rlookupv d1 l   -- rvl_right
rlookupv (Merge _ d1@(TMerge _ _)) l = rlookupv d1 l
rlookupv (TMerge d _) l = rlookupv d l                -- rvl_left_t
rlookupv _ _ = Nothing

-- | @econcat@ (the paper's @δ + δ1@).
econcat :: Exp -> Exp -> Exp
econcat e1 (Merge e3 e4) = Merge (spine e1 e3) e4
econcat e1 (TMerge e3 a) = TMerge (spine e1 e3) a
econcat e1 _ = e1

-- | The left spine of a concatenation: chains recurse, anything else is dropped.
spine :: Exp -> Exp -> Exp
spine e1 e3@(Merge _ _) = econcat e1 e3
spine e1 e3@(TMerge _ _) = econcat e1 e3
spine e1 _ = e1

-- | @big ve e v@.
eval :: Exp -> Exp -> Maybe Exp
eval env = go
  where
    go (Lit n) = pure (Lit n)                                    -- b_lit
    go (Var n) = lookupv env n                                   -- b_var
    go (Lam e) = pure (Clos env e)                               -- b_lam
    go e@(Clos _ _) = pure e                                     -- b_clos
    go (App e1 e2) = do                                          -- b_beta
      Clos env' e <- go e1
      v2 <- go e2
      eval (Merge env' v2) e
    go (TLam e) = pure (TClos env e)                             -- b_blam
    go e@(TClos _ _) = pure e                                    -- b_bclos
    go (TApp e a) = do                                           -- b_tbeta
      TClos env' e1 <- go e
      eval (TMerge env' (TyBoxT (c2g env) a)) e1
    go (Box e1 e2) = go e1 >>= \v1 -> eval v1 e2                 -- b_box
    go Unit = pure Unit                                          -- b_nil
    go (Merge e1 e2) = do                                        -- b_edef
      ve1 <- go e1
      Merge ve1 <$> eval (econcat env ve1) e2
    go (TMerge e1 a) = do                                        -- b_tdef
      ve1 <- go e1
      pure (TMerge ve1 (wrapEnvInTyBox (c2g (econcat env ve1)) a))
    go (Rec l e) = Rec l <$> go e                                -- b_rec
    go (RProj e l) = go e >>= \v -> rlookupv v l                 -- b_proj
    go (Anno e _) = go e
    go (EList es) = EList <$> mapM go es
    go (ETake n e) = do { EList vs <- go e; pure (EList (take n vs)) }
    go (ELength e) = do { EList vs <- go e; pure (Lit (LitInt (length vs))) }
    go (BinOp op) = case op of
      Add a b -> ints (\x y -> LitInt (x + y)) a b
      Sub a b -> ints (\x y -> LitInt (x - y)) a b
      Mul a b -> ints (\x y -> LitInt (x * y)) a b
      LessThan a b -> ints (\x y -> LitBool (x < y)) a b
      EqEq a b -> do
        v1 <- go a
        v2 <- go b
        pure (Lit (LitBool (v1 == v2)))
      where
        ints k a b = do
          Lit (LitInt x) <- go a
          Lit (LitInt y) <- go b
          pure (Lit (k x y))
