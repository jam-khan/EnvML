-- | Type checking for the nameless core: a transcription of the Rocq mechanization
--   (FirstForall/Rocq/exists). Each definition names the Rocq definition it
--   transcribes; contexts are lists with the newest entry at the head, so Rocq's
--   @T +++ T1@ is @t1 ++ t@.
--
--   Only the definitions a checker needs are transcribed: @check@, @lookt@,
--   @tshift@, @keyLen@, @rigid@, @wfe@/@wft@, @teq@, @get_var@, @lb_in@/@mopen@/@rlk@
--   and @has_type@ (as the bidirectional 'infer' / 'check'). Contexts are
--   well-formed by construction, since they are only ever extended with
--   @wft@-checked types, so the @wfe@ premises of the leaf rules are not re-checked.
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

--------------------------------------------------------------------------------
-- Contexts (Teq.v)
--------------------------------------------------------------------------------

-- | @keyLen@: the number of type bindings in a context.
keyLen :: TyEnv -> Int
keyLen [] = 0
keyLen (Type _ : bs) = keyLen bs
keyLen (Kind : bs) = 1 + keyLen bs
keyLen (TypeEq _ : bs) = 1 + keyLen bs

-- | @tshift@: shift the type variables at or above @x@ by one.
tshift :: Int -> Typ -> Typ
tshift _ (TyLit i) = TyLit i
tshift x (TyVar y) = if x <= y then TyVar (1 + y) else TyVar y
tshift x (TyArr a1 a2) = TyArr (tshift x a1) (tshift x a2)
tshift x (TyAll a) = TyAll (tshift (1 + x) a)
tshift _ (TyBoxT t a) = TyBoxT t a
tshift x (TySubstT a1 a2) = TySubstT (tshift x a1) (tshift (1 + x) a2)
tshift x (TyRcd l a) = TyRcd l (tshift x a)
tshift x (TyEnvt bs) = TyEnvt (tshiftBinds x bs)
tshift x (TyList a) = TyList (tshift x a)

tshiftBinds :: Int -> TyEnv -> TyEnv
tshiftBinds _ [] = []
tshiftBinds x (Kind : bs) = Kind : tshiftBinds x bs
tshiftBinds x (Type a : bs) =
  Type (tshift (keyLen bs + x) a) : tshiftBinds x bs
tshiftBinds x (TypeEq a : bs) =
  TypeEq (tshift (keyLen bs + x) a) : tshiftBinds x bs

-- | @check@: the @x@-th type binding is abstract (@⋆@). Positional: term entries
--   are skipped, every type entry counts.
checkAbs :: TyEnv -> Int -> Bool
checkAbs [] _ = False
checkAbs (Type _ : g) x = checkAbs g x
checkAbs (TypeEq _ : g) x = x > 0 && checkAbs g (x - 1)
checkAbs (Kind : g) x = x == 0 || checkAbs g (x - 1)

-- | @lookt@: the definition of the @x@-th type binding when it is manifest,
--   shifted past every type binding crossed on the way.
lookt :: TyEnv -> Int -> Maybe Typ
lookt [] _ = Nothing
lookt (Type _ : t) x = lookt t x
lookt (TypeEq a : _t) 0 = pure (tshift 0 a)
lookt (TypeEq _a : t) x = tshift 0 <$> lookt t (x - 1)
lookt (Kind : _t) 0 = Nothing
lookt (Kind : t) x = tshift 0 <$> lookt t (x - 1)

--------------------------------------------------------------------------------
-- Well-formedness and rigidity (Teq.v: rigid, wfe, wft)
--------------------------------------------------------------------------------

-- | @rigid d T A@: every free type variable of @A@ is either bound by one of the
--   innermost @d@ binders or manifest with a rigid definition.
rigid :: Int -> TyEnv -> Typ -> Bool
rigid _ _ (TyLit _) = True
rigid d g (TyVar x) =
  (checkAbs g x && x < d) || maybe False (rigid d g) (lookt g x)
rigid d g (TyArr a b) = rigid d g a && rigid d g b
rigid d g (TyRcd _ a) = rigid d g a
rigid d g (TyList a) = rigid d g a
rigid d g (TySubstT a b) = rigid (d + 1) (TypeEq a : g) b
rigid d g (TyAll a) = rigid (d + 1) (Kind : g) a
rigid _ _ (TyBoxT g3 a) = rigid 0 g3 a
rigid _ _ (TyEnvt []) = True
rigid d g (TyEnvt (Kind : r)) = rigid d g (TyEnvt r)
rigid d g (TyEnvt (Type a : r)) =
  rigid d g (TyEnvt r) && rigid (d + keyLen r) (r ++ g) a
rigid d g (TyEnvt (TypeEq a : r)) =
  rigid d g (TyEnvt r) && rigid (d + keyLen r) (r ++ g) a

-- | @wfe@: a well-formed context.
wfe :: TyEnv -> Bool
wfe [] = True
wfe (Kind : g) = wfe g
wfe (Type a : g) = wfe g && wftIn g a
wfe (TypeEq a : g) = wfe g && wftIn g a

-- | @wft T A@ (= @wfe (T &= A)@): a well-formed type in a well-formed context.
wft :: TyEnv -> Typ -> Bool
wft g a = wfe g && wftIn g a

-- | The structural part of @wft@ (the @we_*@ clauses), assuming @wfe g@.
wftIn :: TyEnv -> Typ -> Bool
wftIn _ (TyLit _) = True                                         -- we_int
wftIn g (TyVar i) = checkAbs g i || isJust (lookt g i)            -- we_check / we_get
wftIn g (TyArr a b) = wftIn g a && wftIn g b                      -- we_arr
wftIn g (TyAll a) = wftIn (Kind : g) a                            -- we_all
wftIn _ (TyBoxT g3 a) = wfe g3 && wftIn g3 a && rigid 0 g3 a      -- we_box
wftIn g (TySubstT a b) = wftIn g a && wftIn (TypeEq a : g) b      -- we_mani
wftIn _ (TyEnvt []) = True                                        -- we_top
wftIn g (TyEnvt (Kind : r)) = wftIn g (TyEnvt r)                  -- we_ands
wftIn g (TyEnvt (Type a : r)) =                                   -- we_and
  wftIn g (TyEnvt r) && wftIn (r ++ g) a
wftIn g (TyEnvt (TypeEq a : r)) =
  wftIn g (TyEnvt r) && wftIn (r ++ g) a
wftIn g (TyRcd _ a) = wftIn g a                                   -- we_rcd
wftIn g (TyList a) = wftIn g a

--------------------------------------------------------------------------------
-- Type equivalence (Teq.v: teq)
--------------------------------------------------------------------------------

-- | @teq T1 A B T2@. The relation is not syntax-directed: for a given pair of
--   types several rules may apply (a manifest type on either side, a box on either
--   side, a concrete variable on either side), so every applicable rule is tried.
--   Plain recursion terminates because every premise is smaller under the
--   @bindings@ measure of Decide.v.
teq :: TyEnv -> Typ -> Typ -> TyEnv -> Bool
teq g1 a b g2 =
  or [eql, eqr, tvar, manil, manir, boxl, boxr, structural]
  where
    -- eq_eql: a concrete variable on the left is replaced by its definition
    eql = case a of
      TyVar x | Just a' <- lookt g1 x -> teq g1 a' b g2
      _ -> False
    -- eq_eqr
    eqr = case b of
      TyVar y | Just b' <- lookt g2 y -> teq g1 a b' g2
      _ -> False
    -- eq_tvar: the same abstract position on both sides
    tvar = case (a, b) of
      (TyVar x, TyVar y) -> x == y && checkAbs g1 x && checkAbs g2 y
      _ -> False
    -- eq_manil: discharge [A]B into the left context, pad the right with ⋆
    manil = case a of
      TySubstT a1 a2 -> teq (TypeEq a1 : g1) a2 (tshift 0 b) (Kind : g2)
      _ -> False
    -- eq_manir
    manir = case b of
      TySubstT b1 b2 -> teq (Kind : g1) (tshift 0 a) b2 (TypeEq b1 : g2)
      _ -> False
    -- eq_boxl: switch to the box's own context on the left
    boxl = case a of
      TyBoxT g3 a' -> wft g1 a && teq g3 a' b g2
      _ -> False
    -- eq_boxr
    boxr = case b of
      TyBoxT g4 b' -> wft g2 b && teq g1 a b' g4
      _ -> False
    -- eq_int / eq_top / eq_arr / eq_all / eq_and / eq_ands / eq_rcd
    structural = case (a, b) of
      (TyLit l1, TyLit l2) -> l1 == l2
      (TyArr a1 a2, TyArr b1 b2) -> teq g1 a1 b1 g2 && teq g1 a2 b2 g2
      (TyAll a', TyAll b') -> teq (Kind : g1) a' b' (Kind : g2)
      (TyEnvt e1, TyEnvt e2) -> teqEnv g1 e1 e2 g2
      (TyRcd l1 a', TyRcd l2 b') -> l1 == l2 && teq g1 a' b' g2
      (TyList a', TyList b') -> teq g1 a' b' g2
      _ -> False

-- | @eq_and@ / @eq_ands@: environment types entry by entry, each entry under the
--   context extended with the older entries.
teqEnv :: TyEnv -> TyEnv -> TyEnv -> TyEnv -> Bool
teqEnv _ [] [] _ = True
teqEnv g1 (Kind : e1) (Kind : e2) g2 =
  teqEnv g1 e1 e2 g2
teqEnv g1 (Type a : e1) (Type b : e2) g2 =
  teqEnv g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqEnv g1 (TypeEq a : e1) (TypeEq b : e2) g2 =
  teqEnv g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqEnv _ _ _ _ = False

--------------------------------------------------------------------------------
-- Values (ExpSyntax.v: value)
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Lookups (Safety.v: lb_in, mopen, rlk, get_var)
--------------------------------------------------------------------------------

-- | @lb_in@: the label is bound by a record entry of the environment type.
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
  | l == l1 && not (lbIn l g1) = wrapping g1 a                 -- rlk_hit
  | l /= l1 = rlk g1 l                                          -- rlk_left
  | otherwise = Nothing
rlk (Type (TyEnvt t2) : g1) l
  | not (lbIn l g1) = wrapping g1 =<< rlk t2 l                   -- rlk_right
  | otherwise = Nothing
rlk (TypeEq _ : g1) l = rlk g1 l                                 -- rlk_left_t
rlk _ _ = Nothing

-- | @get_var@: the type of the @x@-th term binding, shifted past the type
--   bindings crossed on the way.
getVar :: TyEnv -> Int -> Maybe Typ
getVar [] _ = Nothing
getVar (Kind : g) x = tshift 0 <$> getVar g x
getVar (TypeEq _ : g) x = tshift 0 <$> getVar g x
getVar (Type a : _) 0 = Just a
getVar (Type _ : g) x = getVar g (x - 1)

--------------------------------------------------------------------------------
-- Typing (Safety.v: has_type), bidirectionally
--------------------------------------------------------------------------------

-- | Expose the head constructor of a type at an elimination site, using the
--   equivalences that @t_eq@ admits: a manifest variable is replaced by its
--   definition (@eq_eql@), and a box over the empty context is replaced by its
--   body (@eq_boxl@; the body of such a box is closed).
whnf :: TyEnv -> Typ -> Typ
whnf g = go (0 :: Int)
  where
    go n t
      | n > 200 = t
      | otherwise =
          case t of
            TyBoxT [] a -> go (n + 1) a
            TyVar x | Just a <- lookt g x -> go (n + 1) a
            _ -> t

-- | Only the alias part of 'whnf': a closure's type is a box, so the box must
--   not be peeled when checking one.
unfoldAlias :: TyEnv -> Typ -> Typ
unfoldAlias g = go (0 :: Int)
  where
    go n t
      | n > 200 = t
      | otherwise =
          case t of
            TyVar x | Just a <- lookt g x -> go (n + 1) a
            _ -> t

-- | Infer the type of an expression.
infer :: TyEnv -> Exp -> Maybe Typ
infer _ (Lit lit) = pure $ TyLit $ inferLit lit                 -- t_int
  where
    inferLit (LitInt _) = TyInt
    inferLit (LitBool _) = TyBool
    inferLit (LitStr _) = TyStr
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
infer g (Anno e t) = do                                          -- t_eq (annotation)
  guard (wft g t)
  guard (check g e t)
  return t
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
infer g (BinOp (EqEq e1 e2)) = do
  t1 <- infer g e1
  guard (check g e2 t1)
  return (TyLit TyBool)
infer g (BinOp (LessThan e1 e2)) = do
  guard (check g e1 (TyLit TyInt))
  guard (check g e2 (TyLit TyInt))
  return (TyLit TyBool)

-- List inference
infer _ (EList []) = Nothing -- Cannot infer empty list type
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
  | TyBoxT g1 (TyArr a b) <- unfoldAlias g t =
      case infer [] d of
        Just (TyEnvt g2) ->
          g1 == g2 && value d && rigid 0 g1 (TyArr a b) && check (Type a : g1) e b
        _ -> False
check g (TClos d e) t                                            -- t_bclos
  | TyBoxT g1 (TyAll a) <- unfoldAlias g t =
      case infer [] d of
        Just (TyEnvt g2) ->
          g1 == g2 && value d && rigid 0 g1 (TyAll a) && check (Kind : g1) e a
        _ -> False
check g (App e1 e2) tyB =                                        -- t_app
  case infer g e2 of
    Just tyA  -> check g e1 (TyArr tyA tyB)
    Nothing   -> False
-- List checking
check _ (EList []) (TyList _) = True
check g (EList es) (TyList t) = all (\e -> check g e t) es
check g e t =                                                    -- t_eq
  case infer g e of
    Just t' -> teq g t' t g
    _ -> False
