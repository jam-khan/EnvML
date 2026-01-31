module Core.Check where

import Control.Monad (guard)
import Core.Syntax

-- | Count type variable bindings (Etvar and Eteq) in an environment

{-
    keyLen[·]       = 0
    keyLen[A,  Γ]   = keyLen(Γ)
    keyLen[A=, Γ]   = 1 + keyLen(Γ)
    keyLen[*,  Γ]   = 1 + keyLen(Γ)
-}
keyLen :: TyEnv -> Int
keyLen [] = 0
keyLen (Type _ : bs) = keyLen bs
keyLen (Kind : bs) = 1 + keyLen bs
keyLen (TypeEq _ : bs) = 1 + keyLen bs

-- | Type shifting: shifts type variable indices >= x by 1
--   tshift x typ returns the shifted type

{-
    (x, int)↑   = int
    (x, _y_)↑   = _(1 + y)_ if x <= y
                = _y_       otherwise
    (x, A→B)↑   = (x, A)↑ → (x, B)↑
    (x, ∀A)↑    = ∀. (1 + x, A)↑
    (x, Γ|>A)↑  = Γ|>A
    (x, [A]B)↑  = [(x, A)↑] (1 + x, B)↑
    (x, {l:A})↑ = {l : (x, A)↑}
    (x, Γ)↑     = (x, Γ)c↑
-}
tshift :: Int -> Typ -> Typ
tshift _ (TyLit i) = TyLit i
tshift x (TyVar y) = if x <= y then TyVar (1 + y) else TyVar y
tshift x (TyArr a1 a2) = TyArr (tshift x a1) (tshift x a2)
tshift x (TyAll a) = TyAll (tshift (1 + x) a)
tshift _ (TyBoxT t a) = TyBoxT t a -- BoxT is opaque, no shifting inside
tshift x (TySubstT a1 a2) = TySubstT (tshift x a1) (tshift (1 + x) a2)
tshift x (TyRcd l a) = TyRcd l (tshift x a)
tshift x (TyEnvt bs) = TyEnvt (tshiftBinds x bs)

-- | Helper for shifting bindings in an typing environment

{-
    [·](i)     = ·
    [* , Γ](i) = *, [Γ]i
    [A , Γ](i) = [A](i + |Γ|), [Γ](i)
    [A=, Γ](i) = [A](i + |Γ|)=, [Γ](i)
-}
tshiftBinds :: Int -> TyEnv -> TyEnv
tshiftBinds _ [] = []
tshiftBinds x (Kind : bs) = Kind : tshiftBinds x bs
tshiftBinds x (Type a : bs) =
  Type (tshift (keyLen bs + x) a) : tshiftBinds x bs
tshiftBinds x (TypeEq a : bs) =
  TypeEq (tshift (keyLen bs + x) a) : tshiftBinds x bs

-- | Check if an environment is concrete (contains no Etvar bindings)

{-
    [·](i)      = ⊥
    [A,  Γ](i)  = [Γ](i)
    [A=, Γ](0)  = ⊥
    [A=, Γ](i)  = [Γ](i-1)
    [*,  Γ](0)  = 0
    [*,  Γ](i)  = 1 + [Γ](i - 1)
-}
inner :: TyEnv -> Int -> Maybe Int
inner [] _ = Nothing
inner (Type _ : g) x = inner g x
inner (TypeEq _ : _g) 0 = Nothing
inner (TypeEq _ : g) x = inner g (x - 1)
inner (Kind : _g) 0 = pure 0
inner (Kind : g) x = (+ 1) <$> inner g (x - 1)

-- | Look up a type variable in an environment
--   Returns the type associated with the index, shifted appropriately
lookt :: TyEnv -> Int -> Maybe Typ
lookt [] _ = Nothing
lookt (Type _ : t) x = lookt t x
lookt (TypeEq a : _t) 0 = pure (tshift 0 a)
lookt (TypeEq _a : t) x = tshift 0 <$> lookt t (x - 1)
lookt (Kind : _t) 0 = Nothing
lookt (Kind : t) x = tshift 0 <$> lookt t (x - 1)

{-
    if * ∉ Γ, then Γ is concrete.
-}
concrete :: TyEnv -> Bool
concrete g = and [x /= Kind | x <- g]

teq :: TyEnv -> Typ -> Typ -> TyEnv -> Bool
teq _ (TyLit a) (TyLit b) _ = a == b
teq g1 (TyVar x) b g2 =
  maybe
    ( case b of
        TyVar y -> inner g1 x == inner g2 y
        _ -> False
    )
    (\a -> teq g1 a b g2)
    (lookt g1 x)
teq g1 a (TyVar y) g2 =
  maybe False (\b -> teq g1 a b g2) (lookt g2 y)
teq _g1 (TyBoxT g3 a) b g2 =
  concrete g3 && teq g3 a b g2
teq _g1 a (TyBoxT g3 b) g2 =
  concrete g3 && teq g3 a b g2
teq g1 (TyArr a b) (TyArr c d) g2 =
  teq g1 a c g2 && teq g1 b d g2
teq g1 (TyAll a) (TyAll b) g2 =
  teq (Kind : g1) a b (Kind : g2)
teq g1 (TySubstT a b) c g2 =
  teq (TypeEq a : g1) b c g2
teq g1 b (TySubstT a c) g2 =
  teq g1 b c (TypeEq a : g2)
teq g1 (TyEnvt e1) (TyEnvt e2) g2 =
  teqEnv g1 e1 e2 g2
teq g1 (TyRcd l1 a) (TyRcd l2 b) g2 =
  l1 == l2 && teq g1 a b g2
teq _ _ _ _ = False

-- | Helper for comparing environment types
teqEnv :: TyEnv -> TyEnv -> TyEnv -> TyEnv -> Bool
teqEnv _ [] [] _ = True
teqEnv g1 (Kind : e1) (Kind : e2) g2 =
  teqEnv g1 e1 e2 g2
teqEnv g1 (Type a : e1) (Type b : e2) g2 =
  teqEnv g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqEnv g1 (TypeEq a : e1) (TypeEq b : e2) g2 =
  teqEnv g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqEnv _ _ _ _ = False

value :: Exp -> Bool
value (Lit _) = True
value (Clos e _) = lvalue e
value (TClos e _) = lvalue e
value (FEnv e) = lvalue e
value (Rec _ v) = value v
value _ = False

-- | Check if a closure environment is all values
lvalue :: Env -> Bool
lvalue [] = True
lvalue (ExpE v : e) = lvalue e && value v
lvalue (TypE (TyBoxT _ _) : e) =
  lvalue e
lvalue (TypE _ : _) = False

-- | Check if a label is in an environment type
lbIn :: String -> Typ -> Bool
lbIn l (TyEnvt (Type (TyRcd l' _) : _)) = l == l'
lbIn l (TyEnvt (Type _ : g)) = lbIn l (TyEnvt g)
lbIn l (TyEnvt (TypeEq _ : g)) = lbIn l (TyEnvt g)
lbIn _ _ = False

-- | Wrapping
wrapping :: TyEnv -> Typ -> Maybe Typ
wrapping [] a = Just a
wrapping (Type _ : g) a = wrapping g a
wrapping (TypeEq c : g) a = wrapping g (TySubstT c a)
wrapping (Kind : _) _ = Nothing

-- | Record label lookup in an environment
rlk :: TyEnv -> String -> Maybe Typ
rlk [] _ = Nothing
rlk (Type (TyRcd l1 a) : g1) l
  | l == l1 && not (lbIn l (TyEnvt g1)) = wrapping g1 a -- rlk_hit
  | l /= l1 = rlk g1 l -- rlk_left
  | otherwise = Nothing
rlk (Type (TyEnvt t2) : g1) l
  | not (lbIn l (TyEnvt g1)) = wrapping g1 =<< rlk t2 l
  | otherwise = Nothing
rlk (TypeEq _ : g1) l = rlk g1 l -- rlk_left_t
rlk _ _ = Nothing

-- | Look up a term variable in an environment
--   Etvar/Eteq don't consume the index but require shifting
--   Evar consumes the index
getVar :: TyEnv -> Int -> Maybe Typ
getVar [] _ = Nothing
getVar (Kind : g) x = tshift 0 <$> getVar g x
getVar (TypeEq _ : g) x = tshift 0 <$> getVar g x
getVar (Type a : _) 0 = Just a
getVar (Type _ : g) x = getVar g (x - 1)

-- | Infer the type of an expression
--   Returns Just typ if inference succeeds, Nothing otherwise
infer :: TyEnv -> Exp -> Maybe Typ
infer _ (Lit lit) = pure $ TyLit $ inferLit lit
  where
    inferLit (LitInt _) = TyInt
    inferLit (LitBool _) = TyBool
    inferLit (LitStr _) = TyStr
infer g (Var x) = getVar g x
infer g (App e1 e2) = do
  TyArr a b <- infer g e1
  guard (check g e2 a)
  return b
infer g (TLam e) = TyAll <$> infer (Kind : g) e
infer g (TApp e t) = do
  TyAll b <- infer g e
  return (TySubstT t b)
infer g (Box d e) = do
  TyEnvt g1 <- infer g (FEnv d)
  TyBoxT g1 <$> infer g1 e
infer _ (FEnv []) = pure (TyEnvt [])
infer g (FEnv (ExpE e : d)) = do
  TyEnvt g1 <- infer g (FEnv d)
  a <- infer (g1 ++ g) e
  return (TyEnvt (Type a : g1))
infer g (FEnv (TypE t : d)) = do
  TyEnvt g1 <- infer g (FEnv d)
  return (TyEnvt (TypeEq t : g1))
infer g (Rec l e) = TyRcd l <$> infer g e
infer g (RProj e l) = do
  TyEnvt g1 <- infer g e
  rlk g1 l
infer g (Anno e t) =
  if check g e t then Just t else Nothing
infer g (BinOp (Sub e1 e2)) = do
  guard (check g e1 (TyLit TyInt))
  guard (check g e2 (TyLit TyInt))
  return (TyLit TyInt)
infer g (BinOp (Mul e1 e2)) = do
  guard (check g e1 (TyLit TyInt))
  guard (check g e2 (TyLit TyInt))
  return (TyLit TyInt)
infer g (If e1 e2 e3) = do
  guard (check g e1 (TyLit TyBool))
  t2 <- infer g e2
  t3 <- infer g e3
  guard (teq g t2 t3 g)
  return t2
infer g (BinOp (EqEq e1 e2)) = do
  t1 <- infer g e1
  guard (check g e2 t1)
  return (TyLit TyBool)
infer _ _ = Nothing -- Other cases cannot be inferred

-- | Check an expression against a type
--   Returns True if the expression has the given type
check :: TyEnv -> Exp -> Typ -> Bool
check g (Lam e) (TyArr a b) = check (Type a : g) e b
check g (TLam e) (TyAll a) = check (Kind : g) e a
check g (Clos d e) (TyBoxT g1 (TyArr a b)) =
  case infer g (FEnv d) of
    Just (TyEnvt g2) -> g1 == g2 && lvalue d && check (Type a : g1) e b
    _ -> False
check g (TClos d e) (TyBoxT g1 (TyAll a)) =
  case infer g (FEnv d) of
    Just (TyEnvt g2) -> g1 == g2 && lvalue d && check (Kind : g1) e a
    _ -> False
check g (Fix e) (TyArr a b) =
  check (Type (TyArr a b) : g) e (TyArr a b)
check g e t =
  case infer g e of
    Just t' -> teq g t' t g -- Use type equality
    _ -> False
