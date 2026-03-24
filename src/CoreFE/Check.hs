module CoreFE.Check where

import Control.Monad (guard)
import CoreFE.Syntax
import Debug.Trace (trace, traceM)

-- | Count type variable bindings (Etvar and Eteq) in an environment
keyLen :: TyEnv -> Int
keyLen [] = 0
keyLen (Type _ : bs) = keyLen bs
keyLen (Kind : bs) = 1 + keyLen bs
keyLen (TypeEq _ : bs) = 1 + keyLen bs

-- | Type shifting
tshift :: Int -> Typ -> Typ
tshift _ (TyLit i) = TyLit i
tshift x (TyVar y) = if x <= y then TyVar (1 + y) else TyVar y
tshift x (TyArr a1 a2) = TyArr (tshift x a1) (tshift x a2)
tshift x (TyAll a) = TyAll (tshift (1 + x) a)
tshift _ (TyBoxT t a) = TyBoxT t a
tshift x (TySubstT a1 a2) = TySubstT (tshift x a1) (tshift (1 + x) a2)
tshift x (TyRcd l a) = TyRcd l (tshift x a)
tshift x (TyEnvt bs) = TyEnvt (tshiftBinds x bs)
tshift x (TyList a) = TyList (tshift x a) -- ADD THIS
tshift x (TySum ctors) = TySum [(l, tshift x t) | (l, t) <- ctors]
tshift x (TyMu t) = TyMu (tshift (1 + x) t) -- TODO: Verify

tshiftBinds :: Int -> TyEnv -> TyEnv
tshiftBinds _ [] = []
tshiftBinds x (Kind : bs) = Kind : tshiftBinds x bs
tshiftBinds x (Type a : bs) =
  Type (tshift (keyLen bs + x) a) : tshiftBinds x bs
tshiftBinds x (TypeEq a : bs) =
  TypeEq (tshift (keyLen bs + x) a) : tshiftBinds x bs

inner :: TyEnv -> Int -> Maybe Int
inner [] _ = Nothing
inner (Type _ : g) x = inner g x
inner (TypeEq _ : _g) 0 = Nothing
inner (TypeEq _ : g) x = inner g (x - 1)
inner (Kind : _g) 0 = pure 0
inner (Kind : g) x = (+ 1) <$> inner g (x - 1)

lookt :: TyEnv -> Int -> Maybe Typ
lookt [] _ = Nothing
lookt (Type _ : t) x = lookt t x
lookt (TypeEq a : _t) 0 = pure (tshift 0 a)
lookt (TypeEq _a : t) x = tshift 0 <$> lookt t (x - 1)
lookt (Kind : _t) 0 = Nothing
lookt (Kind : t) x = tshift 0 <$> lookt t (x - 1)

concrete :: TyEnv -> Bool
concrete g = all (/= Kind) g

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
teq g1 a (TyBoxT g3 b) _ =
  concrete g3 && teq g1 a b g3
teq g1 (TyArr a b) (TyArr c d) g2 =
  teq g1 a c g2 && teq g1 b d g2
teq g1 (TyAll a) (TyAll b) g2 =
  teq (Kind : g1) a b (Kind : g2)
teq g1 (TyMu a) (TyMu b) g2 =
  teq (Kind : g1) a b (Kind : g2)
teq g1 (TySubstT a b) c g2 =
  teq (TypeEq a : g1) b c g2
teq g1 b (TySubstT a c) g2 =
  teq g1 b c (TypeEq a : g2)
teq g1 (TyEnvt e1) (TyEnvt e2) g2 =
  teqEnv g1 e1 e2 g2
teq g1 (TyRcd l1 a) (TyRcd l2 b) g2 =
  l1 == l2 && teq g1 a b g2
teq g1 (TySum c1) (TySum c2) g2 =
  length c1 == length c2
    && and
      [ n1 == n2 && teq g1 t1 t2 g2
      | ((n1, t1), (n2, t2)) <- zip c1 c2
      ]
teq g1 (TyList a) (TyList b) g2 =
  -- ADD THIS
  teq g1 a b g2
teq _ _ _ _ = False

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
value (Fold _ v) = value v
value (DataCon _ v) = value v
value (EList es) = all value es -- ADD THIS
value _ = False

lvalue :: Env -> Bool
lvalue [] = True
lvalue (ExpE v : e) = lvalue e && value v
lvalue (RecE _ : e) = lvalue e
lvalue (TypE (TyBoxT _ _) : e) = lvalue e
lvalue (TypE _ : _) = False

lbIn :: String -> Typ -> Bool
lbIn l (TyEnvt (Type (TyRcd l' _) : _)) = l == l'
lbIn l (TyEnvt (Type _ : g)) = lbIn l (TyEnvt g)
lbIn l (TyEnvt (TypeEq _ : g)) = lbIn l (TyEnvt g)
lbIn _ _ = False

wrapping :: TyEnv -> Typ -> Maybe Typ
wrapping [] a = Just a
wrapping (Type _ : g) a = wrapping g a
wrapping (TypeEq c : g) a = wrapping g (TySubstT c a)
wrapping (Kind : _) _ = Nothing

rlk :: TyEnv -> String -> Maybe Typ
rlk [] _ = Nothing
rlk (Type (TyRcd l1 a) : g1) l
  | l == l1 && not (lbIn l (TyEnvt g1)) = wrapping g1 a
  | l /= l1 = rlk g1 l
  | otherwise = Nothing
rlk (Type (TyEnvt t2) : g1) l
  | not (lbIn l (TyEnvt g1)) = wrapping g1 =<< rlk t2 l
  | otherwise = Nothing
rlk (TypeEq _ : g1) l = rlk g1 l
rlk _ _ = Nothing

resolveProjEnv :: TyEnv -> Typ -> Maybe TyEnv
resolveProjEnv _ (TyEnvt env) = Just env
resolveProjEnv g (TyVar x) = lookt g x >>= resolveProjEnv g
resolveProjEnv g (TySubstT s t) = do
  env <- resolveProjEnv g t
  pure (env ++ [TypeEq s])
resolveProjEnv g (TyMu t) = resolveProjEnv g (TySubstT (TyMu t) t)
resolveProjEnv _ _ = Nothing

getVar :: TyEnv -> Int -> Maybe Typ
getVar [] _ = Nothing
getVar (Kind : g) x = tshift 0 <$> getVar g x
getVar (TypeEq _ : g) x = tshift 0 <$> getVar g x
getVar (Type a : _) 0 = Just a
getVar (Type _ : g) x = getVar g (x - 1)

resolveMuBody :: TyEnv -> Typ -> Maybe Typ
resolveMuBody _ (TyMu body) = Just body
resolveMuBody g (TyVar x) = lookt g x >>= resolveMuBody g
resolveMuBody g (TySubstT s t) = do
  body <- resolveMuBody (TypeEq s : g) t
  pure (TySubstT s body)
resolveMuBody _ _ = Nothing

-- | Infer the type of an expression
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
infer g (TLam e) =
    TyAll <$> infer (Kind : g) e
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
infer g (FEnv (RecE e : d)) = do
    TyEnvt g1 <- infer g (FEnv d)
    a <- infer (g1 ++ g) e
    return (TyEnvt (Type a : g1))
infer g (FEnv (TypE t : d)) = do
    TyEnvt g1 <- infer g (FEnv d)
    return (TyEnvt (TypeEq t : g1))
infer g (Rec l e) = TyRcd l <$> infer g e
infer g (RProj e l) = do
  t <- infer g e
  g1 <- resolveProjEnv g t
  rlk g1 l
infer g (Fold t e) = do
  body <- resolveMuBody g t
  guard (check g e (TySubstT t body))
  pure t
infer g (Unfold e) = do
  t <- infer g e
  body <- resolveMuBody g t
  pure (TySubstT t body)
infer g (Anno e t) =
  if check g e t then Just t else Nothing
infer g (BinOp (Add e1 e2)) = do
  guard (check g e1 (TyLit TyInt))
  guard (check g e2 (TyLit TyInt))
  return (TyLit TyInt)
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
infer g (BinOp (Neq e1 e2)) = do
  t1 <- infer g e1
  guard (check g e2 t1)
  return (TyLit TyBool)
infer g (BinOp (Lt e1 e2)) = do
  guard (check g e1 (TyLit TyInt))
  guard (check g e2 (TyLit TyInt))
  return (TyLit TyBool)
infer g (BinOp (Le e1 e2)) = do
  guard (check g e1 (TyLit TyInt))
  guard (check g e2 (TyLit TyInt))
  return (TyLit TyBool)
infer g (BinOp (Gt e1 e2)) = do
  guard (check g e1 (TyLit TyInt))
  guard (check g e2 (TyLit TyInt))
  return (TyLit TyBool)
infer g (BinOp (Ge e1 e2)) = do
  guard (check g e1 (TyLit TyInt))
  guard (check g e2 (TyLit TyInt))
  return (TyLit TyBool)
infer _ (DataCon _ _) = Nothing
infer g (Case e branches) = do
  t <- infer g e
  ctors <- resolveTySum g t
  inferCaseBranches g ctors branches
-- List inference
infer _ (EList []) = Nothing -- Cannot infer empty list type
infer g (EList (e : es)) = do
  t <- infer g e
  -- Check all remaining elements have the same type
  guard (all (\ei -> check g ei t) es)
  return (TyList t)
infer g (ETake _ e) = do
  TyList t <- infer g e
  return (TyList t)
infer _ _ = Nothing

-- | Check an expression against a type
check :: TyEnv -> Exp -> Typ -> Bool
check g e (TySubstT a b) = check (TypeEq a : g) e b
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
check g (DataCon ctor args) ty =
  case resolveTySum g ty of
    Just ctors ->
      case lookup ctor ctors of
        Just payloadTy -> check g args payloadTy
        Nothing -> False
    Nothing -> False
check g (App e1 e2) tyB =
  case infer g e2 of
    Just tyA -> check g e1 (TyArr tyA tyB)
    Nothing -> False
-- List checking
check _ (EList []) (TyList _) = True -- Empty list checks against any list type
check g (EList es) (TyList t) = all (\e -> check g e t) es
check g (FEnv d) (TyEnvt g1) =
  case infer g (FEnv d) of
    Just (TyEnvt g2) -> g1 == g2 && lvalue d
    _ -> False
check g e t =
  case infer g e of
    Just t' -> teq g t' t g
    _ -> 
      trace ("FAILED to check: " ++ show e ++ " against type: " ++ show t ++ ") in " ++ show g) $
      False

inferCaseBranches :: TyEnv -> [(String, Typ)] -> [CaseBranch] -> Maybe Typ
inferCaseBranches _ _ [] = Nothing
inferCaseBranches g ctors (b : rest) = do
  branchTy <- inferCaseBranch g ctors b
  inferRemaining branchTy rest
  pure branchTy
  where
    inferRemaining _ [] = Just ()
    inferRemaining expectedTy (b' : bs) = do
      branchTy' <- inferCaseBranch g ctors b'
      guard (teq g expectedTy branchTy' g)
      inferRemaining expectedTy bs

inferCaseBranch :: TyEnv -> [(String, Typ)] -> CaseBranch -> Maybe Typ
inferCaseBranch g ctors (CaseBranch ctor body) = do
  payloadTy <- payloadTyForBranch ctor ctors
  infer (Type payloadTy : g) body

payloadTyForBranch :: String -> [(String, Typ)] -> Maybe Typ
payloadTyForBranch "_" ctors = firstPayloadTy ctors
payloadTyForBranch ctor ctors = lookup ctor ctors

firstPayloadTy :: [(String, Typ)] -> Maybe Typ
firstPayloadTy [] = Nothing
firstPayloadTy ((_, ty) : _) = Just ty

resolveTySum :: TyEnv -> Typ -> Maybe [(String, Typ)]
resolveTySum _ (TySum ctors) = Just ctors
resolveTySum g (TyVar x) = lookt g x >>= resolveTySum g
resolveTySum g (TySubstT a b) = do
  ctors <- resolveTySum g b
  pure [(name, TySubstT a payloadTy) | (name, payloadTy) <- ctors]
resolveTySum g (TyMu a) = resolveTySum g (TySubstT (TyMu a) a)
resolveTySum _ _ = Nothing