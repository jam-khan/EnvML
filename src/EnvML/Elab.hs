{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant $" #-}
module EnvML.Elab where

import qualified CoreForAll.Syntax as Core
import qualified EnvML.Syntax as EnvML
type ElabError = String

elabTyEnv ::
  EnvML.TyEnv ->
  Core.TyEnv
elabTyEnv = map elabTyEnvE

elabTyEnvE ::
  EnvML.TyEnvE ->
  Core.TyEnvE
elabTyEnvE (EnvML.Type t) = Core.Type $ elabTyp [] t
elabTyEnvE EnvML.Kind = Core.Kind
elabTyEnvE (EnvML.TypeEq t) = Core.TypeEq $ elabTyp [] t

elabModTyp ::
  EnvML.TyEnv ->
  EnvML.ModuleTyp ->
  Core.Typ
elabModTyp _ (EnvML.TySig intf) = Core.TyEnvt $ elabIntf [] intf
elabModTyp _ (EnvML.TyArrowM a sigB) = Core.TyArr (elabTyp [] a) (elabModTyp [] sigB)

elabIntf ::
  EnvML.TyEnv ->
  EnvML.Intf ->
  Core.TyEnv
elabIntf g = map (elabIntfE g)

elabIntfE ::
  EnvML.TyEnv ->
  EnvML.IntfE ->
  Core.TyEnvE
elabIntfE g (EnvML.TyDef t) = Core.Type $ elabTyp g t
elabIntfE g (EnvML.ValDecl ty) = Core.Type $ elabTyp g ty
elabIntfE g (EnvML.ModDecl intf) = Core.Type $ elabTyp g intf
elabIntfE g (EnvML.SigDecl mty) = Core.Type $ elabModTyp g mty

elabTyp ::
  EnvML.TyEnv ->
  EnvML.Typ ->
  Core.Typ
elabTyp _ (EnvML.TyLit i) = Core.TyLit (elabTyLit i)
elabTyp _ (EnvML.TyVar n) = Core.TyVar n
elabTyp env (EnvML.TyArr a1 a2) =
  Core.TyArr (elabTyp env a1) (elabTyp env a2)
elabTyp env (EnvML.TyAll a) =
  Core.TyAll (elabTyp (EnvML.Kind : env) a)
elabTyp env (EnvML.TyBoxT g1 a) =
  Core.TyBoxT (elabTyEnv g1) (elabTyp (g1 ++ env) a)
elabTyp env (EnvML.TySubstT a1 a2) =
  Core.TySubstT (elabTyp env a1) (elabTyp (EnvML.TypeEq a1 : env) a2)
elabTyp env (EnvML.TyRcd l a) =
  Core.TyRcd l (elabTyp env a)
elabTyp _ (EnvML.TyEnvt bs) =
  Core.TyEnvt (elabTyEnv bs)
elabTyp env (EnvML.TyModule mt) = 
    elabModTyp env mt

elabTyLit ::
  EnvML.TyLit ->
  Core.TyLit
elabTyLit EnvML.TyInt = Core.TyInt
elabTyLit EnvML.TyBool = Core.TyBool
elabTyLit EnvML.TyStr = Core.TyStr

elabEnv ::
  EnvML.TyEnv ->
  EnvML.Env ->
  (EnvML.TyEnv, Core.Env)
elabEnv = error "Environments elaboration to do"

elabEnvE ::
  EnvML.TyEnv ->
  EnvML.EnvE ->
  (EnvML.TyEnvE, Core.EnvE)
elabEnvE = error "Environments elaboration to do"

elabInferM ::
  EnvML.TyEnv ->
  EnvML.Module ->
  (EnvML.Typ, Core.Exp)
elabInferM env (EnvML.Functor a m) = error "TODO"
elabInferM env (EnvML.Struct c) = error "TODO"
elabInferM env (EnvML.MApp m1 m2) = error "TODO"
elabInferM env (EnvML.MLink m1 m2) = error "TODO"

keyLen :: EnvML.TyEnv -> Int
keyLen [] = 0
keyLen (EnvML.Type _ : bs) = keyLen bs
keyLen (EnvML.Kind : bs) = 1 + keyLen bs
keyLen (EnvML.TypeEq _ : bs) = 1 + keyLen bs

tshiftBinds :: Int -> EnvML.TyEnv -> EnvML.TyEnv
tshiftBinds _ [] = []
tshiftBinds x (EnvML.Kind : bs) = EnvML.Kind : tshiftBinds x bs
tshiftBinds x (EnvML.Type a : bs) =
  EnvML.Type (tshift (keyLen bs + x) a) : tshiftBinds x bs
tshiftBinds x (EnvML.TypeEq a : bs) =
  EnvML.TypeEq (tshift (keyLen bs + x) a) : tshiftBinds x bs

tshift :: Int -> EnvML.Typ -> EnvML.Typ
tshift _ (EnvML.TyLit i) = EnvML.TyLit i
tshift x (EnvML.TyVar y) = if x <= y then EnvML.TyVar (1 + y) else EnvML.TyVar y
tshift x (EnvML.TyArr a1 a2) = EnvML.TyArr (tshift x a1) (tshift x a2)
tshift x (EnvML.TyAll a) = EnvML.TyAll (tshift (1 + x) a)
tshift _ (EnvML.TyBoxT t a) = EnvML.TyBoxT t a -- aBoxT is opaque, no shifting inside
tshift x (EnvML.TySubstT a1 a2) = EnvML.TySubstT (tshift x a1) (tshift (1 + x) a2)
tshift x (EnvML.TyRcd l a) = EnvML.TyRcd l (tshift x a)
tshift x (EnvML.TyEnvt bs) = EnvML.TyEnvt (tshiftBinds x bs)
tshift x (EnvML.TyModule mt) = error "TODO"

lookt :: EnvML.TyEnv -> Int -> Either ElabError EnvML.Typ
lookt [] _ = Left "Unbound type variable"
lookt (EnvML.Type _ : t) x = lookt t x
lookt (EnvML.TypeEq a : _) 0 = pure (tshift 0 a)
lookt (EnvML.TypeEq _ : t) x = tshift 0 <$> lookt t (x - 1)
lookt (EnvML.Kind : _) 0 = Left "Kind found when looking for type"
lookt (EnvML.Kind : t) x = tshift 0 <$> lookt t (x - 1)

getVar :: EnvML.TyEnv -> Int -> Either ElabError EnvML.Typ
getVar [] _             = Left "Unbound type variable"
getVar (EnvML.Kind : g) x     = tshift 0 <$> getVar g x
getVar (EnvML.TypeEq _ : g) x = tshift 0 <$> getVar g x
getVar (EnvML.Type a : _) 0   = Right a
getVar (EnvML.Type _ : g) x   = getVar g (x - 1)

concrete :: EnvML.TyEnv -> Bool
concrete g = and [x /= EnvML.Kind | x <- g]

inner :: EnvML.TyEnv -> Int -> Maybe Int
inner [] _ = Nothing
inner (EnvML.Type _ : g) x = inner g x
inner (EnvML.TypeEq _ : _g) 0 = Nothing
inner (EnvML.TypeEq _ : g) x = inner g (x - 1)
inner (EnvML.Kind : _g) 0 = pure 0
inner (EnvML.Kind : g) x = (+ 1) <$> inner g (x - 1)

teqEnv :: EnvML.TyEnv -> EnvML.TyEnv -> EnvML.TyEnv -> EnvML.TyEnv -> Bool
teqEnv _ [] [] _ = True
teqEnv g1 (EnvML.Kind : e1) (EnvML.Kind : e2) g2 =
  teqEnv g1 e1 e2 g2
teqEnv g1 (EnvML.Type a : e1) (EnvML.Type b : e2) g2 =
  teqEnv g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqEnv g1 (EnvML.TypeEq a : e1) (EnvML.TypeEq b : e2) g2 =
  teqEnv g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqEnv _ _ _ _ = False

teq :: EnvML.TyEnv -> EnvML.Typ -> EnvML.Typ -> EnvML.TyEnv -> Bool
teq _ (EnvML.TyLit a) (EnvML.TyLit b) _ = a == b
teq g1 (EnvML.TyVar x) b g2 =
  case lookt g1 x of
    Right a ->
      teq g1 a b g2
    Left _ ->
      case b of
        EnvML.TyVar y -> inner g1 x == inner g2 y
        _ -> False
teq g1 a (EnvML.TyVar y) g2 =
  case lookt g2 y of
    Right b -> teq g1 a b g2
    Left _ -> False
teq _g1 (EnvML.TyBoxT g3 a) b g2 =
  concrete g3 && teq g3 a b g2
teq _g1 a (EnvML.TyBoxT g3 b) g2 =
  concrete g3 && teq g3 a b g2
teq g1 (EnvML.TyArr a b) (EnvML.TyArr c d) g2 =
  teq g1 a c g2 && teq g1 b d g2
teq g1 (EnvML.TyAll a) (EnvML.TyAll b) g2 =
  teq (EnvML.Kind : g1) a b (EnvML.Kind : g2)
teq g1 (EnvML.TySubstT a b) c g2 =
  teq (EnvML.TypeEq a : g1) b c g2
teq g1 b (EnvML.TySubstT a c) g2 =
  teq g1 b c (EnvML.TypeEq a : g2)
teq g1 (EnvML.TyEnvt e1) (EnvML.TyEnvt e2) g2 =
  teqEnv g1 e1 e2 g2
teq g1 (EnvML.TyRcd l1 a) (EnvML.TyRcd l2 b) g2 =
  l1 == l2 && teq g1 a b g2
teq _ _ _ _ = False

value :: EnvML.Exp -> Bool
value (EnvML.Lit _) = True
value (EnvML.Clos e _) = lvalue e
value (EnvML.TClos e _) = lvalue e
value (EnvML.FEnv e) = lvalue e
value (EnvML.Rec _ v) = value v
value _ = False

lvalue :: EnvML.Env -> Bool
lvalue [] = True
lvalue (EnvML.ExpE v : e) = lvalue e && value v
lvalue (EnvML.TypE (EnvML.TyBoxT _ _) : e) =
  lvalue e
lvalue (EnvML.TypE _ : _) = False

lbIn :: String -> EnvML.Typ -> Bool
lbIn l (EnvML.TyEnvt (EnvML.Type (EnvML.TyRcd l' _) : _)) = l == l'
lbIn l (EnvML.TyEnvt (EnvML.Type _ : g)) = lbIn l (EnvML.TyEnvt g)
lbIn l (EnvML.TyEnvt (EnvML.TypeEq _ : g)) = lbIn l (EnvML.TyEnvt g)
lbIn _ _ = False

wrapping :: EnvML.TyEnv -> EnvML.Typ -> Maybe EnvML.Typ
wrapping [] a = Just a
wrapping (EnvML.Type _ : g) a = wrapping g a
wrapping (EnvML.TypeEq c : g) a = wrapping g (EnvML.TySubstT c a)
wrapping (EnvML.Kind : _) _ = Nothing

rlk :: EnvML.TyEnv -> String -> Maybe EnvML.Typ
rlk [] _ = Nothing
rlk (EnvML.Type (EnvML.TyRcd l1 a) : g1) l
  | l == l1 && not (lbIn l (EnvML.TyEnvt g1)) = wrapping g1 a -- rlk_hit
  | l /= l1 = rlk g1 l -- rlk_left
  | otherwise = Nothing
rlk (EnvML.Type (EnvML.TyEnvt t2) : g1) l
  | not (lbIn l (EnvML.TyEnvt g1)) = wrapping g1 =<< rlk t2 l
  | otherwise = Nothing
rlk (EnvML.TypeEq _ : g1) l = rlk g1 l -- rlk_left_t
rlk _ _ = Nothing

elabExpCheck ::
  EnvML.TyEnv ->
  EnvML.Exp ->
  EnvML.Typ ->
  Either ElabError Core.Exp
elabExpCheck env (EnvML.Lam e) (EnvML.TyArr a b) = do
  e' <- elabExpCheck (EnvML.Type a : env) e b
  Right $ Core.Lam e'
elabExpCheck env (EnvML.TLam e) (EnvML.TyAll a) = do
  e' <- elabExpCheck (EnvML.Kind : env) e a
  Right $ Core.Lam e'
elabExpCheck env (EnvML.Clos d e) (EnvML.TyBoxT g1 (EnvML.TyArr a b))
  | not (lvalue d) = Left "Closure environment is not all values"
  | otherwise = do
      e' <- elabExpCheck (EnvML.Type a : g1) e b
      d' <- elabExpCheck env (EnvML.FEnv d) (EnvML.TyEnvt g1)
      case d' of
        Core.FEnv d'' -> pure $ Core.Clos d'' e'
        _ -> Left "Expected FEnv in elaboration of closure"
elabExpCheck env (EnvML.TClos d e) (EnvML.TyBoxT g1 (EnvML.TyAll a))
  | not (lvalue d) = Left "Type Closure environment is not all values"
  | otherwise = do
      e' <- elabExpCheck (EnvML.Kind : g1) e a
      d' <- elabExpCheck env (EnvML.FEnv d) (EnvML.TyEnvt g1)
      case d' of
        Core.FEnv d'' -> pure $ Core.TClos d'' e'
        _ -> Left "Expected FEnv in elaboration of type closure"
elabExpCheck env (EnvML.ModE m) (EnvML.TyModule mt) = error "TODO"
elabExpCheck env e ty =
  do
    (ty', e') <- elabExpInfer env e
    if teq env ty' ty env
      then Right e'
      else Left $ "Type mismatch in elaboration check: expected " ++ show ty ++ ", got " ++ show ty'

elabExpInfer ::
  EnvML.TyEnv ->
  EnvML.Exp ->
  Either ElabError (EnvML.Typ, Core.Exp)
elabExpInfer _ (EnvML.Lit l) =
  case l of
    EnvML.LitInt n -> Right $ (EnvML.TyLit EnvML.TyInt, Core.Lit (Core.LitInt n))
    EnvML.LitBool b -> Right $ (EnvML.TyLit EnvML.TyBool, Core.Lit (Core.LitBool b))
    EnvML.LitStr s -> Right $ (EnvML.TyLit EnvML.TyStr, Core.Lit (Core.LitStr s))
elabExpInfer env (EnvML.Var n) = do
  t <- getVar env n
  Right (t, Core.Var n) 
elabExpInfer env (EnvML.App e1 e2) = do
  (ty1, e1') <- elabExpInfer env e1
  case ty1 of
    EnvML.TyArr a b -> do
      e2' <- elabExpCheck env e2 a
      Right (b, Core.App e1' e2')
    _ -> Left "Expected function type in application"
elabExpInfer env (EnvML.TApp e t) =
  do
    (ty, e') <- elabExpInfer env e
    case ty of
      EnvML.TyAll a -> Right (EnvML.TySubstT t a, Core.TApp e' (elabTyp [] t))
      _ -> Left "Expected universal type in type application"
elabExpInfer env (EnvML.TLam e) = do
  (t, e') <- elabExpInfer (EnvML.Kind : env) e
  Right (EnvML.TyAll t, Core.TLam e')
elabExpInfer env (EnvML.Box d e) = do
  dd <- elabExpInfer env (EnvML.FEnv d)
  case dd of
    (EnvML.TyEnvt g1, Core.FEnv d') -> do
      (te, e') <- elabExpInfer g1 e
      Right (EnvML.TyBoxT g1 te, Core.Box d' e')
    _ -> Left "Expected environment type in box"
elabExpInfer env (EnvML.Rec l e) =
  do
    (te, e') <- elabExpInfer env e
    Right (EnvML.TyRcd l te, Core.Rec l e')
elabExpInfer env (EnvML.RProj e l) =
  do
    (ty, e') <- elabExpInfer env e
    case ty of
      EnvML.TyEnvt g1 ->
        case rlk g1 l of
          Just t -> Right (t, Core.RProj e' l)
          Nothing -> Left "Label not found in record projection"
      _ -> Left "Expected environment type in record projection"
elabExpInfer env (EnvML.FEnv (EnvML.ExpE e : d)) =
  case elabExpInfer env (EnvML.FEnv d) of
    Right (EnvML.TyEnvt g1, Core.FEnv d') -> do
      (te, e') <- elabExpInfer (g1 ++ env) e
      Right (EnvML.TyEnvt (EnvML.Type te : g1), Core.FEnv (Core.ExpE e' : d'))
    _ -> Left "Expected environment type in FEnv"
elabExpInfer env (EnvML.FEnv (EnvML.TypE t : d)) =
  case elabExpInfer env (EnvML.FEnv d) of
    Right (EnvML.TyEnvt g1, Core.FEnv d') ->
      let t' = elabTyp (g1 ++ env) t
       in Right (EnvML.TyEnvt (EnvML.TypeEq t : g1), Core.FEnv (Core.TypE t' : d'))
    _ -> Left "Expected environment type in FEnv"
elabExpInfer _ (EnvML.FEnv []) =
  Right (EnvML.TyEnvt [], Core.FEnv [])
elabExpInfer env (EnvML.Anno e t) =
  do
    e' <- elabExpCheck env e t
    Right (t, Core.Anno e' (elabTyp [] t))
elabExpInfer env e = Left $ "Cannot infer type for expression: " ++ show e 
