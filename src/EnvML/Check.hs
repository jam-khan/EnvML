module EnvML.Check where

import Control.Monad (guard)
import qualified CoreFE.Syntax as CoreFE
import EnvML.Syntax (Name, Typ(..), TyCtxE(..), TyCtx, ModuleTyp(..), FunArg(..), Intf, IntfE(..))
import qualified EnvML.Desugared as D

typeSubstName :: Name -> Typ -> Typ -> Typ
typeSubstName _ _ (TyLit l) = TyLit l
typeSubstName name s (TyVar n)
  | n == name = s
  | otherwise = TyVar n
typeSubstName name s (TyArr a b) = TyArr (typeSubstName name s a) (typeSubstName name s b)
typeSubstName name s (TyAll n body)
  | n == name = TyAll n body
  | otherwise = TyAll n (typeSubstName name s body)
typeSubstName name s (TyBoxT ctx t) = TyBoxT (tyCtxSubstName name s ctx) (typeSubstName name s t)
typeSubstName name s (TyRcd fs) = TyRcd [(l, typeSubstName name s t) | (l, t) <- fs]
typeSubstName name s (TySum cs) = TySum [(l, typeSubstName name s t) | (l, t) <- cs]
typeSubstName name s (TyMu n body)
  | n == name = TyMu n body
  | otherwise = TyMu n (typeSubstName name s body)
typeSubstName name s (TyList t) = TyList (typeSubstName name s t)
typeSubstName name s (TyCtx ctx) = TyCtx (tyCtxSubstName name s ctx)
typeSubstName name s (TyModule mty) = TyModule (substModTypName name s mty)

tyCtxSubstName :: Name -> Typ -> TyCtx -> TyCtx
tyCtxSubstName _ _ [] = []
tyCtxSubstName name s (TypeN n t : rest)
  | n == name = TypeN n t : rest
  | otherwise = TypeN n (typeSubstName name s t) : tyCtxSubstName name s rest
tyCtxSubstName name s (KindN n : rest)
  | n == name = KindN n : rest
  | otherwise = KindN n : tyCtxSubstName name s rest
tyCtxSubstName name s (TypeEqN n t : rest)
  | n == name = TypeEqN n (typeSubstName name s t) : rest
  | otherwise = TypeEqN n (typeSubstName name s t) : tyCtxSubstName name s rest
tyCtxSubstName _ _ (Type _ : _) = error "Unnamed Type in TyCtx not supported."
tyCtxSubstName _ _ (Kind : _) = error "Unnamed Kind in TyCtx not supported."
tyCtxSubstName name s (e : rest) = e : tyCtxSubstName name s rest

lookupTypeEq :: TyCtx -> Name -> Maybe Typ
lookupTypeEq [] _ = Nothing
lookupTypeEq (TypeEqN n t : _) x | n == x = Just t
lookupTypeEq (KindN n : _) x | n == x = Nothing  -- KindN shadows TypeEqN
lookupTypeEq (Type _ : _) _ = error "Unnamed Type in TyCtx not supported."
lookupTypeEq (Kind : _) _ = error "Unnamed Kind in TyCtx not supported."
lookupTypeEq (_ : g) x = lookupTypeEq g x

concrete :: TyCtx -> Bool
concrete = not . any isKindOrUnsupported
  where
    isKindOrUnsupported (KindN _) = True
    isKindOrUnsupported Kind      = error "Unnamed Kind in TyCtx not supported."
    isKindOrUnsupported (Type _)  = error "Unnamed Type in TyCtx not supported."
    isKindOrUnsupported _         = False

teq :: TyCtx -> Typ -> Typ -> TyCtx -> Bool
teq _ (TyLit a) (TyLit b) _ = a == b
teq g1 (TyVar x) b g2 =
  case lookupTypeEq g1 x of
    Just a -> teq g1 a b g2
    Nothing -> case b of
      TyVar y -> case lookupTypeEq g2 y of
        Just b' -> teq g1 (TyVar x) b' g2
        Nothing -> x == y
      _ -> False
teq g1 a (TyVar y) g2 =
  case lookupTypeEq g2 y of
    Just b -> teq g1 a b g2
    Nothing -> False
teq g1 (TyArr a b) (TyArr c d) g2 =
  teq g1 a c g2 && teq g1 b d g2
teq g1 (TyAll n1 a) (TyAll n2 b) g2 =
  teq (KindN n1 : g1) a (typeSubstName n2 (TyVar n1) b) (KindN n1 : g2)
teq _g1 (TyBoxT ctx a) b g2 =
  concrete ctx && teq ctx a b g2
teq g1 a (TyBoxT ctx b) _g2 =
  concrete ctx && teq g1 a b ctx
teq g1 (TyRcd fs1) (TyRcd fs2) g2 =
  length fs1 == length fs2
    && all (\((l1, t1), (l2, t2)) -> l1 == l2 && teq g1 t1 t2 g2) (zip fs1 fs2)
teq g1 (TySum cs1) (TySum cs2) g2 =
  length cs1 == length cs2
    && all (\((l1, t1), (l2, t2)) -> l1 == l2 && teq g1 t1 t2 g2) (zip cs1 cs2)
teq g1 (TyMu n1 a) (TyMu n2 b) g2 =
  teq (KindN n1 : g1) a (typeSubstName n2 (TyVar n1) b) (KindN n1 : g2)
teq g1 (TyList a) (TyList b) g2 =
  teq g1 a b g2
teq g1 (TyCtx ctx1) (TyCtx ctx2) g2 =
  teqCtx g1 ctx1 ctx2 g2
teq g1 (TyModule m1) (TyModule m2) g2 =
  mtyEq g1 m1 m2 g2
teq _ _ _ _ = False

teqCtx :: TyCtx -> TyCtx -> TyCtx -> TyCtx -> Bool
teqCtx _ [] [] _ = True
teqCtx g1 (KindN _ : e1) (KindN _ : e2) g2 =
  teqCtx g1 e1 e2 g2
teqCtx g1 (TypeN _ a : e1) (TypeN _ b : e2) g2 =
  teqCtx g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqCtx g1 (TypeEqN _ a : e1) (TypeEqN _ b : e2) g2 =
  teqCtx g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqCtx _ (Type _ : _) _ _ = error "Unnamed Type in TyCtx not supported."
teqCtx _ _ (Type _ : _) _ = error "Unnamed Type in TyCtx not supported."
teqCtx _ (Kind : _) _ _ = error "Unnamed Kind in TyCtx not supported."
teqCtx _ _ (Kind : _) _ = error "Unnamed Kind in TyCtx not supported."
teqCtx _ _ _ _ = False

getVar :: TyCtx -> Name -> Maybe Typ
getVar [] _ = Nothing
getVar (TypeN n a : _) x | n == x = Just a
getVar (TyMod n mty : _) x | n == x = Just (TyModule mty)
getVar (Type _ : _) _ = error "Unnamed Type in TyCtx not supported."
getVar (Kind : _) _ = error "Unnamed Kind in TyCtx not supported."
getVar (_ : g) x = getVar g x

lookupModTypeEq :: TyCtx -> Name -> Maybe ModuleTyp
lookupModTypeEq [] _ = Nothing
lookupModTypeEq (TypeEqM n mty : _) x | n == x = Just mty
lookupModTypeEq (Type _ : _) _ = error "Unnamed Type in TyCtx not supported."
lookupModTypeEq (Kind : _) _ = error "Unnamed Kind in TyCtx not supported."
lookupModTypeEq (_ : g) x = lookupModTypeEq g x

lookupIntf :: Name -> Intf -> Maybe Typ
lookupIntf l intf = go intf
  where
    go [] = Nothing
    go (TyDef n t : rest)
      | n == l    = Just t
      | otherwise = fmap (typeSubstName n t) (go rest)
    go (ValDecl n t : _) | n == l = Just t
    go (ModDecl n t : _) | n == l = Just t
    go (FunctorDecl n _ t : _) | n == l = Just t
    go (SigDecl n i : _) | n == l = Just (TyModule (TySig i))
    go (_ : rest) = go rest

infer :: TyCtx -> D.Exp -> Maybe Typ
infer _ (D.Lit lit) = pure $ TyLit $ inferLit lit
  where
    inferLit (CoreFE.LitInt _) = CoreFE.TyInt
    inferLit (CoreFE.LitBool _) = CoreFE.TyBool
    inferLit (CoreFE.LitStr _) = CoreFE.TyStr
    inferLit CoreFE.LitUnit = CoreFE.TyUnit
infer g (D.Var x) = getVar g x
infer g (D.App e1 e2) = do
  TyArr a b <- infer g e1
  guard (check g e2 a)
  return b
infer g (D.TLam name e) = TyAll name <$> infer (KindN name : g) e
infer g (D.TApp e t) = do
  TyAll name b <- infer g e
  return (typeSubstName name t b)
infer g (D.Box d e) = do
  TyCtx g1 <- infer g (D.FEnv d)
  TyBoxT g1 <$> infer g1 e
infer _ (D.FEnv []) = pure (TyCtx [])
infer _ (D.FEnv (D.ExpE _ : _)) = error "Unnamed exp elements in FEnvs at source not supported currently."
infer g (D.FEnv (D.ExpEN name e : d)) = do
  TyCtx g1 <- infer g (D.FEnv d)
  a <- infer (g1 ++ g) e
  return (TyCtx (TypeN name a : g1))
infer _ (D.FEnv (D.TypE _ : _)) = error "Unnamed type elements in FEnvs at source not supported currently."
infer g (D.FEnv (D.TypEN name t : d)) = do
  TyCtx g1 <- infer g (D.FEnv d)
  return (TyCtx (TypeN name t : g1))
infer g (D.FEnv (D.ModE name m : d)) = do
  TyCtx g1 <- infer g (D.FEnv d)
  mty <- inferMod g m
  return (TyCtx (TyMod name mty : g1))
infer g (D.FEnv (D.ModTypE name mty : d)) = do
  TyCtx g1 <- infer g (D.FEnv d)
  return (TyCtx (TypeEqM name mty : g1))
infer _ (D.Rec []) = pure $ TyRcd []
infer g (D.Rec ((name, e) : rest)) = do
  a <- infer g e
  TyRcd ts <- infer g (D.Rec rest)
  return $ TyRcd ((name, a) : ts)
infer g (D.RProj e l) = do
  t <- infer g e
  projType t
  where
    projType (TyRcd fields) = lookup l fields
    projType (TyModule (TySig intf)) = lookupIntf l intf
    projType _ = Nothing
infer g (D.Anno e t) =
  if check g e t then Just t else Nothing
infer g (D.Mod m) = TyModule <$> inferMod g m
infer g (D.BinOp (D.Add e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyInt)
infer g (D.BinOp (D.Sub e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyInt)
infer g (D.BinOp (D.Mul e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyInt)
infer g (D.If e1 e2 e3) = do
  guard (check g e1 (TyLit CoreFE.TyBool))
  t2 <- infer g e2
  t3 <- infer g e3
  guard (teq g t2 t3 g)
  return t2
infer g (D.BinOp (D.EqEq e1 e2)) = do
  t1 <- infer g e1
  guard (check g e2 t1)
  return (TyLit CoreFE.TyBool)
infer g (D.BinOp (D.Neq e1 e2)) = do
  t1 <- infer g e1
  guard (check g e2 t1)
  return (TyLit CoreFE.TyBool)
infer g (D.BinOp (D.Lt e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyBool)
infer g (D.BinOp (D.Le e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyBool)
infer g (D.BinOp (D.Gt e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyBool)
infer g (D.BinOp (D.Ge e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyBool)
infer g (D.DataCon ctor payload ty) = do
  ctors <- resolveTySum g ty
  payloadTy <- lookup ctor ctors
  guard (check g payload payloadTy)
  return ty
infer g (D.Fold ty e) =
  case resolveToMu g ty of
    Just (n, body) ->
      let unfolded = typeSubstName n ty body
       in if check g e unfolded then Just ty else Nothing
    Nothing -> Nothing
infer g (D.Unfold e) = do
  t <- infer g e
  unfoldMu g t
infer g (D.Case e branches) = do
  t <- infer g e
  ctors <- resolveTySum g t
  inferCaseBranches g ctors branches
infer _ (D.EList []) = Nothing -- Cannot infer empty list type
infer g (D.EList (e : es)) = do
  t <- infer g e
  guard (all (\ei -> check g ei t) es)
  return (TyList t)
infer g (D.ETake _ e) = do
  TyList t <- infer g e
  return (TyList t)
infer _ _ = Nothing

inferMod :: TyCtx -> D.Module -> Maybe ModuleTyp
inferMod g (D.VarM name) = getMod g name
inferMod g (D.Struct structs) = TySig <$> inferStructs g structs
inferMod g (D.Functor name TyArg m) = do
  mty <- inferMod (KindN name : g) m
  return $ ForallM name mty
inferMod g (D.Functor name (TmArgType ty) m) = do
  mty <- inferMod (bindModEntry name ty : g) m
  return $ TyArrowM ty mty
inferMod _ (D.Functor _ TmArg _) = Nothing
inferMod g (D.MApp m1 m2) = do
  TyArrowM a mty <- inferMod g m1
  guard (check g (D.Mod m2) a)
  return mty
inferMod g (D.MAppt m1 ty) = do
  ForallM name mty <- inferMod g m1
  return (substModTypName name ty mty)
inferMod g (D.MAnno m mty) = do
  guard (checkMod g m mty)
  return mty

getMod :: TyCtx -> Name -> Maybe ModuleTyp
getMod [] _ = Nothing
getMod (TyMod n mty : _) x | n == x = Just mty
getMod (Type _ : _) _ = error "Unnamed Type in TyCtx not supported."
getMod (Kind : _) _ = error "Unnamed Kind in TyCtx not supported."
getMod (_ : g) x = getMod g x

bindModEntry :: Name -> Typ -> TyCtxE
bindModEntry name (TyModule mty) = TyMod name mty
bindModEntry name ty = TypeN name ty

inferStructs :: TyCtx -> D.Structures -> Maybe Intf
inferStructs g ss = inferStructs' g (reverse ss)

inferStructs' :: TyCtx -> D.Structures -> Maybe Intf
inferStructs' _ [] = Just []
inferStructs' g (s : rest) = do
  (entry, g') <- inferStructure g s
  entries <- inferStructs' g' rest
  return (entry : entries)

inferStructure :: TyCtx -> D.Structure -> Maybe (IntfE, TyCtx)
inferStructure g (D.Let name Nothing e) = do
  t <- infer g e
  return (ValDecl name t, TypeN name t : g)
inferStructure g (D.Let name (Just ty) e) = do
  guard (check g e ty)
  return (ValDecl name ty, TypeN name ty : g)
inferStructure g (D.TypDecl name ty) =
  Just (TyDef name ty, TypeEqN name ty : g)
inferStructure g (D.ModTypDecl name mty) = case mty of
  TySig intf -> Just (SigDecl name intf, TypeEqM name mty : g)
  _ -> Just (SigDecl name [], TypeEqM name mty : g)
inferStructure g (D.ModStruct name Nothing m) = do
  mty <- inferMod g m
  return (ModDecl name (TyModule mty), TyMod name mty : g)
inferStructure g (D.ModStruct name (Just mty) m) = do
  guard (checkMod g m mty)
  return (ModDecl name (TyModule mty), TyMod name mty : g)

checkMod :: TyCtx -> D.Module -> ModuleTyp -> Bool
checkMod g m (TyVarM name) =
  case lookupModTypeEq g name of
    Just mty -> checkMod g m mty
    Nothing -> False
checkMod g (D.Functor name (TmArgType ty) m) (TyArrowM a mty) =
  teq g ty a g && checkMod (bindModEntry name a : g) m mty
checkMod g (D.Functor name TmArg m) (TyArrowM a mty) =
  checkMod (bindModEntry name a : g) m mty
checkMod g (D.Functor name TyArg m) (ForallM n mty) =
  checkMod (KindN name : g) m (substModTypName n (TyVar name) mty)
checkMod g (D.Struct structs) (TySig intf) =
  case inferStructs g structs of
    Just inferred -> intfEq g inferred intf g
    Nothing -> False
checkMod g m mty =
  case inferMod g m of
    Just mty' -> mtyEq g mty' mty g
    Nothing -> False

check :: TyCtx -> D.Exp -> Typ -> Bool
check g (D.Lam name mty e) (TyArr a b) =
  case mty of
    Just t  -> teq g t a g && check (TypeN name a : g) e b
    Nothing -> check (TypeN name a : g) e b
check g (D.TLam name e) (TyAll n b) =
  check (KindN name : g) e (typeSubstName n (TyVar name) b)
check g (D.Fix f e) (TyArr a b) =
  check (TypeN f (TyArr a b) : g) e (TyArr a b)
check g (D.Clos d e) (TyBoxT ctx ty) =
  case infer g (D.FEnv d) of
    Just (TyCtx ctx') -> teqCtx g ctx' ctx g && check ctx e ty
    _ -> False
check _ (D.TClos {}) (TyBoxT _ _) =
  error "Typed closures not supported at source currently."
check g (D.DataCon ctor payload _) ty =
  case resolveTySum g ty of
    Just ctors -> case lookup ctor ctors of
      Just payloadTy -> check g payload payloadTy
      Nothing -> False
    Nothing -> False
check _ (D.EList []) (TyList _) = True
check g (D.EList es) (TyList t) = all (\e -> check g e t) es
check g e t =
  case infer g e of
    Just t' -> teq g t' t g
    _ -> False

resolveTySum :: TyCtx -> Typ -> Maybe [(Name, Typ)]
resolveTySum _ (TySum ctors) = Just ctors
resolveTySum g (TyVar x) =
  lookupTypeEq g x >>= resolveTySum g
resolveTySum _ _ = Nothing

unfoldMu :: TyCtx -> Typ -> Maybe Typ
unfoldMu _ (TyMu n body) = Just (typeSubstName n (TyMu n body) body)
unfoldMu g (TyVar x) = lookupTypeEq g x >>= unfoldMu g
unfoldMu _ _ = Nothing

resolveToMu :: TyCtx -> Typ -> Maybe (Name, Typ)
resolveToMu _ (TyMu n body) = Just (n, body)
resolveToMu g (TyVar x) = lookupTypeEq g x >>= resolveToMu g
resolveToMu _ _ = Nothing

inferCaseBranches :: TyCtx -> [(Name, Typ)] -> [D.CaseBranch] -> Maybe Typ
inferCaseBranches _ _ [] = Nothing
inferCaseBranches g ctors (b : bs) = do
  t <- inferCaseBranch g ctors b
  mapM_
    ( \br -> do
        t' <- inferCaseBranch g ctors br
        guard (teq g t t' g)
    )
    bs
  return t

inferCaseBranch :: TyCtx -> [(Name, Typ)] -> D.CaseBranch -> Maybe Typ
inferCaseBranch g _ (D.CaseBranch "_" _ body) = infer g body
inferCaseBranch g ctors (D.CaseBranch ctor binder body) = do
  payloadTy <- lookup ctor ctors
  infer (TypeN binder payloadTy : g) body

mtyEq :: TyCtx -> ModuleTyp -> ModuleTyp -> TyCtx -> Bool
mtyEq g1 (TyVarM n) m2 g2 =
  case lookupModTypeEq g1 n of
    Just mty -> mtyEq g1 mty m2 g2
    Nothing -> case m2 of
      TyVarM m -> case lookupModTypeEq g2 m of
        Just mty -> mtyEq g1 (TyVarM n) mty g2
        Nothing -> n == m
      _ -> False
mtyEq g1 m1 (TyVarM n) g2 =
  case lookupModTypeEq g2 n of
    Just mty -> mtyEq g1 m1 mty g2
    Nothing -> False
mtyEq g1 (TyArrowM a1 m1) (TyArrowM a2 m2) g2 =
  teq g1 a1 a2 g2 && mtyEq g1 m1 m2 g2
mtyEq g1 (ForallM n1 m1) (ForallM n2 m2) g2 =
  mtyEq (KindN n1 : g1) m1 (substModTypName n2 (TyVar n1) m2) (KindN n1 : g2)
mtyEq g1 (TySig i1) (TySig i2) g2 = intfEq g1 i1 i2 g2
mtyEq _ _ _ _ = False

intfEq :: TyCtx -> Intf -> Intf -> TyCtx -> Bool
intfEq _ [] [] _ = True
intfEq g1 (TyDef n1 t1 : r1) (TyDef n2 t2 : r2) g2 =
  n1 == n2 && teq g1 t1 t2 g2 && intfEq (TypeEqN n1 t1 : g1) r1 r2 (TypeEqN n2 t2 : g2)
intfEq g1 (ValDecl n1 t1 : r1) (ValDecl n2 t2 : r2) g2 =
  n1 == n2 && teq g1 t1 t2 g2 && intfEq (TypeN n1 t1 : g1) r1 r2 (TypeN n2 t2 : g2)
intfEq g1 (ModDecl n1 t1 : r1) (ModDecl n2 t2 : r2) g2 =
  n1 == n2 && teq g1 t1 t2 g2 && intfEq g1 r1 r2 g2
intfEq g1 (FunctorDecl n1 _ t1 : r1) (FunctorDecl n2 _ t2 : r2) g2 =
  n1 == n2 && teq g1 t1 t2 g2 && intfEq g1 r1 r2 g2
intfEq g1 (SigDecl n1 i1 : r1) (SigDecl n2 i2 : r2) g2 =
  n1 == n2 && intfEq g1 i1 i2 g2 && intfEq g1 r1 r2 g2
intfEq _ _ _ _ = False

substModTypName :: Name -> Typ -> ModuleTyp -> ModuleTyp
substModTypName name s (TyArrowM ty mty) =
  TyArrowM (typeSubstName name s ty) (substModTypName name s mty)
substModTypName name s (ForallM n mty)
  | n == name = ForallM n mty
  | otherwise = ForallM n (substModTypName name s mty)
substModTypName name s (TySig intf) = TySig (substIntfName name s intf)
substModTypName _ _ (TyVarM n) = TyVarM n

substIntfName :: Name -> Typ -> Intf -> Intf
substIntfName _ _ [] = []
substIntfName name s (TyDef n ty : rest) =
  TyDef n (typeSubstName name s ty) : substIntfName name s rest
substIntfName name s (ValDecl n ty : rest) =
  ValDecl n (typeSubstName name s ty) : substIntfName name s rest
substIntfName name s (ModDecl n ty : rest) =
  ModDecl n (typeSubstName name s ty) : substIntfName name s rest
substIntfName name s (FunctorDecl n args ty : rest) =
  FunctorDecl n args (typeSubstName name s ty) : substIntfName name s rest
substIntfName name s (SigDecl n intf : rest) =
  SigDecl n (substIntfName name s intf) : substIntfName name s rest