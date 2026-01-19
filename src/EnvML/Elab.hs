{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant $" #-}
module EnvML.Elab where

import qualified CoreForAll.Syntax as Core
import qualified EnvML.Syntax as EnvML
import Control.Monad (unless)
type ElabError = String

elabTyEnv ::
  EnvML.TyEnv 
  -> EnvML.TyEnv
  -> Either ElabError Core.TyEnv
elabTyEnv _g []   = pure []
elabTyEnv g (x:xs)= do
  x'  <- elabTyEnvE g x
  xs' <- elabTyEnv (x:g) xs
  Right $ x':xs'

elabTyEnvE ::
  EnvML.TyEnv
  -> EnvML.TyEnvE
  -> Either ElabError Core.TyEnvE
elabTyEnvE g (EnvML.Type t)   = Core.Type   <$> elabTyp g t
elabTyEnvE _g EnvML.Kind      = pure Core.Kind
elabTyEnvE g (EnvML.TypeEq t) = Core.TypeEq <$> elabTyp g t

elabModTyp ::
  EnvML.TyEnv
  -> EnvML.ModuleTyp
  -> Either ElabError Core.Typ
elabModTyp g (EnvML.TySig intf)       = Core.TyEnvt <$> elabIntf g intf
elabModTyp g (EnvML.TyArrowM a sigB)  = Core.TyArr <$> elabTyp g a <*> elabModTyp g sigB

elabIntf ::
  EnvML.TyEnv ->
  EnvML.Intf ->
  Either ElabError Core.TyEnv
elabIntf g = mapM (elabIntfE g)

elabIntfE ::
  EnvML.TyEnv ->
  EnvML.IntfE ->
  Either ElabError Core.TyEnvE
elabIntfE g (EnvML.TyDef t)       = Core.Type <$> elabTyp g t
elabIntfE g (EnvML.ValDecl ty)    = Core.Type <$> elabTyp g ty
elabIntfE g (EnvML.ModDecl intf)  = Core.Type <$> elabTyp g intf
elabIntfE g (EnvML.SigDecl mty)   = Core.Type <$> elabModTyp g mty

elabTyp ::
  EnvML.TyEnv 
  -> EnvML.Typ
  -> Either ElabError Core.Typ
elabTyp _ (EnvML.TyLit i)         =
  pure $ Core.TyLit (elabTyLit i)
elabTyp _ (EnvML.TyVar n)         =
  pure $ Core.TyVar n
elabTyp g (EnvML.TyArr a1 a2)     =
  Core.TyArr <$> elabTyp g a1 <*> elabTyp g a2
elabTyp g (EnvML.TyAll a)         =
  Core.TyAll <$> elabTyp (EnvML.Kind : g) a
elabTyp g (EnvML.TyBoxT g1 a)     =
  Core.TyBoxT <$> elabTyEnv g g1 <*> elabTyp (g1 ++ g) a
elabTyp g (EnvML.TySubstT a1 a2)  =
  Core.TySubstT <$> elabTyp g a1 <*> elabTyp (EnvML.TypeEq a1 : g) a2
elabTyp g (EnvML.TyRcd l a)       =
  Core.TyRcd l <$> elabTyp g a
elabTyp g (EnvML.TyEnvt bs)       =
  Core.TyEnvt <$> elabTyEnv g bs
elabTyp g (EnvML.TyModule mt) = 
    elabModTyp g mt

elabTyLit ::
  EnvML.TyLit ->
  Core.TyLit
elabTyLit EnvML.TyInt   = Core.TyInt
elabTyLit EnvML.TyBool  = Core.TyBool
elabTyLit EnvML.TyStr   = Core.TyStr

elabInferM ::
  EnvML.TyEnv ->
  EnvML.Module ->
  (EnvML.Typ, Core.Exp)
elabInferM env (EnvML.Functor a m)  = error "TODO"
elabInferM env (EnvML.Struct c)     = error "TODO"
elabInferM env (EnvML.MApp m1 m2)   = error "TODO"
elabInferM env (EnvML.MLink m1 m2)  = error "TODO"

-- Here, three cases
-- 
elabEnv ::
  EnvML.TyEnv ->
  EnvML.Env ->
  Either ElabError (EnvML.TyEnv, Core.Env)
elabEnv _env []     = Right $ ([], [])
elabEnv env (x:xs)  = do
  (etyp, etm) <- elabEnvE env x
  let env'    = etyp:env
  (tyEnv', xs') <- elabEnv env' xs
  -- Note: 
  Right $ (etyp : tyEnv', etm:xs')
  -- 1. get `(environment type, elaborated environment term)` from `elaborate x`
  -- 2. add environment type to current env
  -- 3. elaborate remaining elements under new typing context
  -- 4. concatenate result and send back

elabEnvE ::
  EnvML.TyEnv ->
  EnvML.EnvE ->
  Either ElabError (EnvML.TyEnvE, Core.EnvE)
elabEnvE env (EnvML.ExpE e) = error "Expression elaboration in environment to do."
elabEnvE env (EnvML.TypE t) = error "Type elaboration in environment to do."

elabExpCheck ::
  EnvML.TyEnv ->
  EnvML.Exp ->
  EnvML.Typ ->
  Either ElabError Core.Exp
elabExpCheck g (EnvML.Lam e) (EnvML.TyArr a b)  =
  Core.Lam  <$> elabExpCheck (EnvML.Type a : g) e b
elabExpCheck g (EnvML.TLam e) (EnvML.TyAll a)   =
  Core.TLam <$> elabExpCheck (EnvML.Kind : g) e a
elabExpCheck g (EnvML.Clos d e) (EnvML.TyBoxT g1 (EnvML.TyArr a b)) = do
  unless (lvalue d) $
    Left "Closure environment must contain only values"
  (g2, d') <- elabEnv g d
  unless (g1 == g2) $
    Left "Closure environment type does not match the box environment"
  e' <- elabExpCheck (EnvML.Type a : g1) e b
  pure $ Core.Clos d' e'
elabExpCheck env (EnvML.TClos d e) (EnvML.TyBoxT g1 (EnvML.TyAll a)) = do
  unless (lvalue d) $ 
    Left "Type Closure environment is not all values"
  e' <- elabExpCheck (EnvML.Kind : g1) e a
  d' <- elabExpCheck env (EnvML.FEnv d) (EnvML.TyEnvt g1)
  case d' of
    Core.FEnv d'' -> pure $ Core.TClos d'' e'
    _ -> Left "Expected FEnv in elaboration of type closure"
elabExpCheck env (EnvML.ModE m) (EnvML.TyModule mt) = error "TODO"
elabExpCheck env e ty = do
  (ty', e') <- elabExpInfer env e
  if teq env ty' ty env
    then Right e'
    else Left $ "Type mismatch in elaboration check: expected " ++ show ty ++ ", got " ++ show ty'

elabLit ::
  EnvML.Literal
  -> (EnvML.TyLit, Core.Literal)
elabLit (EnvML.LitInt i)  = (EnvML.TyInt,   Core.LitInt i)
elabLit (EnvML.LitBool b) = (EnvML.TyBool,  Core.LitBool b)
elabLit (EnvML.LitStr s)  = (EnvML.TyStr,   Core.LitStr s)

elabExpInfer ::
  EnvML.TyEnv ->
  EnvML.Exp ->
  Either ElabError (EnvML.Typ, Core.Exp)
elabExpInfer _ (EnvML.Lit l)    =
  let (tyLit, tmLit) = elabLit l
  in  Right $ (EnvML.TyLit tyLit, Core.Lit tmLit)
elabExpInfer env (EnvML.Var n)  = do
  t <- getVar env n
  Right (t, Core.Var n) 
elabExpInfer env (EnvML.App e1 e2) = do
  (ty1, e1') <- elabExpInfer env e1
  case ty1 of
    EnvML.TyArr a b -> do
      e2' <- elabExpCheck env e2 a
      Right (b, Core.App e1' e2')
    _ -> Left "Expected function type in application"
elabExpInfer g (EnvML.TApp e t) =
  do
    (ty, e') <- elabExpInfer g e
    case ty of
      EnvML.TyAll a -> do
        t' <- elabTyp g t
        Right (EnvML.TySubstT t a, Core.TApp e' t')
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
    Right (EnvML.TyEnvt g1, Core.FEnv d') -> do
      t' <- elabTyp (g1 ++ env) t
      Right (EnvML.TyEnvt (EnvML.TypeEq t : g1), Core.FEnv (Core.TypE t' : d'))
    _ -> Left "Expected environment type in FEnv"
elabExpInfer _ (EnvML.FEnv []) =
  Right (EnvML.TyEnvt [], Core.FEnv [])
elabExpInfer g (EnvML.Anno e t)   = do
    e' <- elabExpCheck g e t
    t' <- elabTyp g t
    Right (t, Core.Anno e' t')
elabExpInfer env e = Left $ "Cannot infer type for expression: " ++ show e 


{- Utilities -}

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

tshift :: 
  Int 
  -> EnvML.Typ 
  -> EnvML.Typ
tshift _ (EnvML.TyLit i)        = 
  EnvML.TyLit i
tshift x (EnvML.TyVar y)        = 
  if x <= y then EnvML.TyVar (1 + y) else EnvML.TyVar y
tshift x (EnvML.TyArr a1 a2)    = 
  EnvML.TyArr (tshift x a1) (tshift x a2)
tshift x (EnvML.TyAll a)        = 
  EnvML.TyAll (tshift (1 + x) a)
tshift _ (EnvML.TyBoxT t a)     =
  EnvML.TyBoxT t a -- aBoxT is opaque, no shifting inside
tshift x (EnvML.TySubstT a1 a2) = 
  EnvML.TySubstT (tshift x a1) (tshift (1 + x) a2)
tshift x (EnvML.TyRcd l a)      = 
  EnvML.TyRcd l (tshift x a)
tshift x (EnvML.TyEnvt bs)      = 
  EnvML.TyEnvt (tshiftBinds x bs)
tshift x (EnvML.TyModule mt)    = error "TODO"

lookt :: 
  EnvML.TyEnv 
  -> Int 
  -> Either ElabError EnvML.Typ
lookt [] _ = Left "Unbound type variable"
lookt (EnvML.Type _ : t) x    = 
  lookt t x
lookt (EnvML.TypeEq a : _) 0  = 
  pure (tshift 0 a)
lookt (EnvML.TypeEq _ : t) x  = 
  tshift 0 <$> lookt t (x - 1)
lookt (EnvML.Kind : _) 0      = 
  Left "Kind found when looking for type"
lookt (EnvML.Kind : t) x      = 
  tshift 0 <$> lookt t (x - 1)

getVar :: EnvML.TyEnv -> Int -> Either ElabError EnvML.Typ
getVar [] _                   = Left "Unbound type variable"
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
