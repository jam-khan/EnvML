-- | Type checking for the nameless core, transcribing mech/fe_calculus (Teq.v,
--   Safety.v). Contexts are lists, newest entry first, so Rocq's @T +++ T1@ is
--   @t1 ++ t@; each definition is marked with the Rocq rule it comes from.
module CoreFE.Check where

import Control.Monad (guard)
import Data.Maybe (isJust)
import CoreFE.Syntax
    ( TyEnvE(Kind, TypeEq, Type),
      Exp(..),
      Typ(..),
      TyLit(TyBool, TyStr, TyInt),
      Literal(LitStr, LitInt, LitBool),
      BinOp(EqEq, Add, Sub, Mul, LessThan),
      TyEnv )

-- | The type an environment entry carries, if it carries one.
entryTyp :: TyEnvE -> Maybe Typ
entryTyp (Type a)   = Just a
entryTyp (TypeEq a) = Just a
entryTyp Kind       = Nothing

-- | @keyLen@: number of type bindings (@Kind@ and @TypeEq@).
keyLen :: TyEnv -> Int
keyLen = length . filter isTypeBinding
  where isTypeBinding (Type _) = False
        isTypeBinding _        = True

-- | @tshift@: shift type variables at or above @x@.
tshift :: Int -> Typ -> Typ
tshift _ (TyLit i) = TyLit i
tshift x (TyVar y) = TyVar (if x <= y then 1 + y else y)
tshift x (TyArr a b) = TyArr (tshift x a) (tshift x b)
tshift x (TyAll a) = TyAll (tshift (1 + x) a)
tshift _ (TyBoxT t a) = TyBoxT t a
tshift x (TySubstT a b) = TySubstT (tshift x a) (tshift (1 + x) b)
tshift x (TyRcd l a) = TyRcd l (tshift x a)
tshift x (TyEnvt bs) = TyEnvt (tshiftBinds x bs)
tshift x (TyList a) = TyList (tshift x a)

tshiftBinds :: Int -> TyEnv -> TyEnv
tshiftBinds _ [] = []
tshiftBinds x (Kind : bs) = Kind : tshiftBinds x bs
tshiftBinds x (Type a : bs) = Type (tshift (keyLen bs + x) a) : tshiftBinds x bs
tshiftBinds x (TypeEq a : bs) = TypeEq (tshift (keyLen bs + x) a) : tshiftBinds x bs

-- | @check@: the @x@-th type binding is abstract. Term entries are skipped.
checkAbs :: TyEnv -> Int -> Bool
checkAbs [] _ = False
checkAbs (Type _ : g) x = checkAbs g x
checkAbs (TypeEq _ : g) x = x > 0 && checkAbs g (x - 1)
checkAbs (Kind : g) x = x == 0 || checkAbs g (x - 1)

-- | @lookt@: definition of the @x@-th type binding when manifest, shifted past
--   every type binding crossed.
lookt :: TyEnv -> Int -> Maybe Typ
lookt [] _ = Nothing
lookt (Type _ : t) x = lookt t x
lookt (TypeEq a : _) 0 = pure (tshift 0 a)
lookt (TypeEq _ : t) x = tshift 0 <$> lookt t (x - 1)
lookt (Kind : _) 0 = Nothing
lookt (Kind : t) x = tshift 0 <$> lookt t (x - 1)

-- | @rigid d T A@: every free type variable of @A@ is bound by one of the
--   innermost @d@ binders, or manifest with a rigid definition.
rigid :: Int -> TyEnv -> Typ -> Bool
rigid _ _ (TyLit _) = True
rigid d g (TyVar x) = (checkAbs g x && x < d) || maybe False (rigid d g) (lookt g x)
rigid d g (TyArr a b) = rigid d g a && rigid d g b
rigid d g (TyRcd _ a) = rigid d g a
rigid d g (TyList a) = rigid d g a
rigid d g (TySubstT a b) = rigid (d + 1) (TypeEq a : g) b
rigid d g (TyAll a) = rigid (d + 1) (Kind : g) a
rigid _ _ (TyBoxT g3 a) = rigid 0 g3 a
rigid _ _ (TyEnvt []) = True
rigid d g (TyEnvt (e : r)) =
  rigid d g (TyEnvt r) && all (rigid (d + keyLen r) (r ++ g)) (entryTyp e)

-- | @wfe@: a well-formed context.
wfe :: TyEnv -> Bool
wfe [] = True
wfe (e : g) = wfe g && all (wftIn g) (entryTyp e)

-- | @wft T A@ (= @wfe (T &= A)@).
wft :: TyEnv -> Typ -> Bool
wft g a = wfe g && wftIn g a

-- | The @we_*@ clauses, assuming the context is well formed.
wftIn :: TyEnv -> Typ -> Bool
wftIn _ (TyLit _) = True
wftIn g (TyVar i) = checkAbs g i || isJust (lookt g i)
wftIn g (TyArr a b) = wftIn g a && wftIn g b
wftIn g (TyAll a) = wftIn (Kind : g) a
wftIn _ (TyBoxT g3 a) = wfe g3 && wftIn g3 a && rigid 0 g3 a
wftIn g (TySubstT a b) = wftIn g a && wftIn (TypeEq a : g) b
wftIn _ (TyEnvt []) = True
wftIn g (TyEnvt (e : r)) = wftIn g (TyEnvt r) && all (wftIn (r ++ g)) (entryTyp e)
wftIn g (TyRcd _ a) = wftIn g a
wftIn g (TyList a) = wftIn g a

-- | @teq T1 A B T2@. Not syntax-directed (a manifest type, a box or a concrete
--   variable on either side each admit a rule), so every applicable rule is
--   tried; recursion terminates by the @bindings@ measure of Decide.v.
teq :: TyEnv -> Typ -> Typ -> TyEnv -> Bool
teq g1 a b g2 = or [eql, eqr, tvar, manil, manir, boxl, boxr, structural]
  where
    eql = case a of                                              -- eq_eql
      TyVar x -> maybe False (\a' -> teq g1 a' b g2) (lookt g1 x)
      _ -> False
    eqr = case b of                                              -- eq_eqr
      TyVar y -> maybe False (\b' -> teq g1 a b' g2) (lookt g2 y)
      _ -> False
    tvar = case (a, b) of                                        -- eq_tvar
      (TyVar x, TyVar y) -> x == y && checkAbs g1 x && checkAbs g2 y
      _ -> False
    manil = case a of                                            -- eq_manil
      TySubstT a1 a2 -> teq (TypeEq a1 : g1) a2 (tshift 0 b) (Kind : g2)
      _ -> False
    manir = case b of                                            -- eq_manir
      TySubstT b1 b2 -> teq (Kind : g1) (tshift 0 a) b2 (TypeEq b1 : g2)
      _ -> False
    boxl = case a of                                             -- eq_boxl
      TyBoxT g3 a' -> wft g1 a && teq g3 a' b g2
      _ -> False
    boxr = case b of                                             -- eq_boxr
      TyBoxT g4 b' -> wft g2 b && teq g1 a b' g4
      _ -> False
    structural = case (a, b) of      -- eq_int/top/arr/all/and/ands/rcd
      (TyLit l1, TyLit l2) -> l1 == l2
      (TyArr a1 a2, TyArr b1 b2) -> teq g1 a1 b1 g2 && teq g1 a2 b2 g2
      (TyAll a', TyAll b') -> teq (Kind : g1) a' b' (Kind : g2)
      (TyEnvt e1, TyEnvt e2) -> teqEnv g1 e1 e2 g2
      (TyRcd l1 a', TyRcd l2 b') -> l1 == l2 && teq g1 a' b' g2
      (TyList a', TyList b') -> teq g1 a' b' g2
      _ -> False

-- | @eq_and@/@eq_ands@: entrywise, each entry under the older entries.
teqEnv :: TyEnv -> TyEnv -> TyEnv -> TyEnv -> Bool
teqEnv _ [] [] _ = True
teqEnv g1 (x : e1) (y : e2) g2 = teqEnv g1 e1 e2 g2 && sameEntry
  where
    sameEntry = case (x, y) of
      (Kind, Kind) -> True
      (Type a, Type b) -> under a b
      (TypeEq a, TypeEq b) -> under a b
      _ -> False
    under a b = teq (e1 ++ g1) a b (e2 ++ g2)
teqEnv _ _ _ _ = False

-- | @value@ (ExpSyntax.v).
value :: Exp -> Bool
value (Lit _) = True
value (Clos d _) = value d
value (TClos d _) = value d
value (Rec _ v) = value v
value Unit = True
value (Merge d v) = value d && value v
value (TMerge d (TyBoxT _ _)) = value d
value (EList es) = all value es
value _ = False

-- | @lb_in@: the label is bound by a record entry.
lbIn :: String -> TyEnv -> Bool
lbIn l (Type (TyRcd l' _) : g) = l == l' || lbIn l g
lbIn l (Type _ : g) = lbIn l g
lbIn l (TypeEq _ : g) = lbIn l g
lbIn _ _ = False

-- | @mopen@: wrap a type with the manifest bindings of the entries before it.
wrapping :: TyEnv -> Typ -> Maybe Typ
wrapping [] a = Just a
wrapping (Type _ : g) a = wrapping g a
wrapping (TypeEq c : g) a = wrapping g (TySubstT c a)
wrapping (Kind : _) _ = Nothing

-- | @rlk@: label lookup on an environment type.
rlk :: TyEnv -> String -> Maybe Typ
rlk [] _ = Nothing
rlk (Type (TyRcd l1 a) : g1) l
  | l == l1 && not (lbIn l g1) = wrapping g1 a                   -- rlk_hit
  | l /= l1 = rlk g1 l                                           -- rlk_left
  | otherwise = Nothing
rlk (Type (TyEnvt t2) : g1) l                                    -- rlk_right
  | not (lbIn l g1) = wrapping g1 =<< rlk t2 l
  | otherwise = Nothing
rlk (TypeEq _ : g1) l = rlk g1 l                                 -- rlk_left_t
rlk _ _ = Nothing

-- | @get_var@: type of the @x@-th term binding, shifted past type bindings.
getVar :: TyEnv -> Int -> Maybe Typ
getVar [] _ = Nothing
getVar (Kind : g) x = tshift 0 <$> getVar g x
getVar (TypeEq _ : g) x = tshift 0 <$> getVar g x
getVar (Type a : _) 0 = Just a
getVar (Type _ : g) x = getVar g (x - 1)

-- | Expose a type's head using the equivalences @t_eq@ admits: unfold a
--   manifest alias, and with @peelBox@ an empty box (a closure's own type is a
--   box, so checking one must not peel).
reduceTyp :: Bool -> TyEnv -> Typ -> Typ
reduceTyp peelBox g = go (200 :: Int)
  where
    go 0 t = t
    go n t = case t of
      TyBoxT [] a | peelBox -> go (n - 1) a
      TyVar x | Just a <- lookt g x -> go (n - 1) a
      _ -> t

whnf, unfoldAlias :: TyEnv -> Typ -> Typ
whnf = reduceTyp True
unfoldAlias = reduceTyp False

-- | Infer the type of an expression.
infer :: TyEnv -> Exp -> Maybe Typ
infer _ (Lit (LitInt _)) = pure (TyLit TyInt)                    -- t_int
infer _ (Lit (LitBool _)) = pure (TyLit TyBool)
infer _ (Lit (LitStr _)) = pure (TyLit TyStr)
infer g (Var x) = getVar g x                                     -- t_var
infer g (App e1 e2) = do                                         -- t_app
  TyArr a b <- whnf g <$> infer g e1
  guard (check g e2 a)
  return b
infer g (TLam e) = TyAll <$> infer (Kind : g) e                  -- t_blam
infer g (TApp e t) = do                                          -- t_tapp
  TyAll b <- whnf g <$> infer g e
  guard (wft g t)
  return (TySubstT t b)
infer g (Box d e) = do                                           -- t_box
  TyEnvt g1 <- whnf g <$> infer g d
  a <- infer g1 e
  guard (rigid 0 g1 a)
  return (TyBoxT g1 a)
infer _ Unit = pure (TyEnvt [])                                  -- lt_nil
infer g (Merge d e) = do                                         -- lt_conse
  TyEnvt g1 <- whnf g <$> infer g d
  a <- infer (g1 ++ g) e
  return (TyEnvt (Type a : g1))
infer g (TMerge d t) = do                                        -- lt_const
  TyEnvt g1 <- whnf g <$> infer g d
  guard (wft (g1 ++ g) t)
  return (TyEnvt (TypeEq t : g1))
infer g (Rec l e) = TyRcd l <$> infer g e                        -- t_rec
infer g (RProj e l) = do                                         -- trproj
  TyEnvt g1 <- whnf g <$> infer g e
  rlk g1 l
infer g (Anno e t) = do                                          -- t_eq
  guard (wft g t && check g e t)
  return t
infer g (BinOp op) = case op of
  Add a b -> arith a b (TyLit TyInt)
  Sub a b -> arith a b (TyLit TyInt)
  Mul a b -> arith a b (TyLit TyInt)
  LessThan a b -> arith a b (TyLit TyBool)
  EqEq a b -> do
    t <- infer g a
    guard (check g b t)
    return (TyLit TyBool)
  where
    arith a b res = do
      guard (check g a (TyLit TyInt) && check g b (TyLit TyInt))
      return res
infer _ (EList []) = Nothing   -- an empty list has no inferable element type
infer g (EList (e:es)) = do
  t <- infer g e
  guard (all (\ei -> check g ei t) es)
  return (TyList t)
infer g (ETake _ e) = do
  TyList t <- infer g e
  return (TyList t)
infer g (ELength e) = do
  TyList _ <- infer g e
  return (TyLit TyInt)
infer _ _ = Nothing

-- | Check an expression against a type.
check :: TyEnv -> Exp -> Typ -> Bool
check g (Lam e) t                                                -- t_lam
  | TyArr a b <- whnf g t = check (Type a : g) e b
check g (TLam e) t                                               -- t_blam
  | TyAll a <- whnf g t = check (Kind : g) e a
check g (Clos d e) t                                             -- t_clos
  | TyBoxT g1 ab@(TyArr a b) <- unfoldAlias g t =
      closureEnv g1 d && rigid 0 g1 ab && check (Type a : g1) e b
check g (TClos d e) t                                            -- t_bclos
  | TyBoxT g1 al@(TyAll a) <- unfoldAlias g t =
      closureEnv g1 d && rigid 0 g1 al && check (Kind : g1) e a
check g (App e1 e2) tyB =                                        -- t_app
  maybe False (\tyA -> check g e1 (TyArr tyA tyB)) (infer g e2)
check _ (EList []) (TyList _) = True
check g (EList es) (TyList t) = all (\e -> check g e t) es
check g e t =                                                    -- t_eq
  maybe False (\t' -> teq g t' t g) (infer g e)

-- | A closure's environment is a value typed by the closure's own context.
closureEnv :: TyEnv -> Exp -> Bool
closureEnv g1 d = infer [] d == Just (TyEnvt g1) && value d
