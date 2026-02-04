{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module EnvML.Elab where

import qualified Core.Syntax as Core
import qualified EnvML.Syntax as EnvML

type ElabError = String

elabTyEnv ::
  EnvML.TyEnv ->
  Either ElabError Core.TyEnv
elabTyEnv [] = pure []
elabTyEnv (x : xs) = do
  x' <- elabTyEnvE x
  xs' <- elabTyEnv xs
  Right $ x' : xs'

elabTyEnvE ::
  EnvML.TyEnvE ->
  Either ElabError Core.TyEnvE
elabTyEnvE (EnvML.Type t) =
  Core.Type <$> elabTyp t
elabTyEnvE EnvML.Kind =
  pure Core.Kind
elabTyEnvE (EnvML.TypeEq t) =
  Core.TypeEq <$> elabTyp t

elabModTyp ::
  EnvML.ModuleTyp ->
  Either ElabError Core.Typ
elabModTyp (EnvML.TySig intf)       = Core.TyEnvt <$> elabIntf intf
elabModTyp (EnvML.TyArrowM a sigB)  = Core.TyArr <$> elabTyp a <*> elabModTyp sigB
elabModTyp (EnvML.ForallM sig)      = Core.TyAll <$> elabModTyp sig
elabModTyp (EnvML.TyVarM i)         = pure $ Core.TyVar i

elabIntf ::
  EnvML.Intf ->
  Either ElabError Core.TyEnv
elabIntf = mapM elabIntfE

elabIntfE ::
  EnvML.IntfE ->
  Either ElabError Core.TyEnvE
elabIntfE (EnvML.TyDef t)       = Core.TypeEq <$> elabTyp t    -- type t = int
elabIntfE (EnvML.ValDecl ty)    = Core.Type <$> elabTyp ty     -- val x : int
elabIntfE (EnvML.ModDecl intf)  = Core.TypeEq <$> elabTyp intf -- module M : SIG
elabIntfE (EnvML.SigDecl mty)   = Core.TypeEq <$> elabTyp mty  -- signature S = SIG

elabTyp ::
  EnvML.Typ ->
  Either ElabError Core.Typ
elabTyp (EnvML.TyLit i)   =
  pure $ Core.TyLit (elabTyLit i)
elabTyp (EnvML.TyVar n)   =
  pure $ Core.TyVar n
elabTyp (EnvML.TyArr a1 a2) =
  Core.TyArr <$> elabTyp a1 <*> elabTyp a2
elabTyp (EnvML.TyAll a)   =
  Core.TyAll <$> elabTyp a
elabTyp (EnvML.TyBoxT g1 a) =
  Core.TyBoxT <$> elabTyEnv g1 <*> elabTyp a
elabTyp (EnvML.TySubstT a1 a2) =
  Core.TySubstT <$> elabTyp a1 <*> elabTyp a2
elabTyp (EnvML.TyRcd []) = Left "Single records not allowed"
elabTyp (EnvML.TyRcd [(n, t)]) =
  Core.TyRcd n <$> elabTyp t
elabTyp (EnvML.TyRcd fields) = do
  fields' <- traverse elabField fields
  pure $ Core.TyEnvt fields'
  where
    elabField (x, t) = Core.Type . Core.TyRcd x <$> elabTyp t
elabTyp (EnvML.TyEnvt bs) =
  Core.TyEnvt <$> elabTyEnv bs
elabTyp (EnvML.TyModule mt) =
  elabModTyp mt

elabTyLit ::
  EnvML.TyLit ->
  Core.TyLit
elabTyLit EnvML.TyInt = Core.TyInt
elabTyLit EnvML.TyBool = Core.TyBool
elabTyLit EnvML.TyStr = Core.TyStr

elabEnv ::
  EnvML.Env ->
  Either ElabError Core.Env
elabEnv [] = pure []
elabEnv (x : xs) = do
  etm <- elabEnvE x
  xs' <- elabEnv xs
  Right $ etm : xs'

elabM ::
  EnvML.Module ->
  Either ElabError Core.Exp
elabM (EnvML.VarM i) = pure $ Core.Var i
elabM (EnvML.Functor m) = Core.Lam <$> elabM m
elabM (EnvML.Functort m) = Core.TLam <$> elabM m
elabM (EnvML.Struct env) = Core.FEnv <$> elabEnv env
elabM (EnvML.MApp m1 m2) = Core.App <$> elabM m1 <*> elabM m2
elabM (EnvML.MAppt m t) = Core.TApp <$> elabM m <*> elabTyp t
elabM (EnvML.MAnno m mt) = Core.Anno <$> elabM m <*> elabModTyp mt

elabEnvE ::
  EnvML.EnvE ->
  Either ElabError Core.EnvE
elabEnvE (EnvML.ExpE e) = Core.ExpE <$> elabExp e
elabEnvE (EnvML.TypE t) = Core.TypE <$> elabTyp t
elabEnvE (EnvML.ModExpE e) = Core.ExpE <$> elabExp e
elabEnvE (EnvML.ModTypE t) = Core.TypE <$> elabTyp t

elabLit ::
  EnvML.Literal ->
  Core.Literal
elabLit (EnvML.LitInt i) = Core.LitInt i
elabLit (EnvML.LitBool b) = Core.LitBool b
elabLit (EnvML.LitStr s) = Core.LitStr s

elabExp ::
  EnvML.Exp ->
  Either ElabError Core.Exp
elabExp (EnvML.Lit lit)     = pure $ Core.Lit $ elabLit lit
elabExp (EnvML.Var i)       = pure $ Core.Var i
elabExp (EnvML.Lam e)       = Core.Lam <$> elabExp e
elabExp (EnvML.Clos e1 e2)  = Core.Clos <$> elabEnv e1 <*> elabExp e2
elabExp (EnvML.App e1 e2)   = Core.App <$> elabExp e1 <*> elabExp e2
elabExp (EnvML.TLam e)      = Core.TLam <$> elabExp e
elabExp (EnvML.TClos env e) = Core.TClos <$> elabEnv env <*> elabExp e
elabExp (EnvML.TApp e ty)   = Core.TApp <$> elabExp e <*> elabTyp ty
elabExp (EnvML.Box env ty)  = Core.Box <$> elabEnv env <*> elabExp ty
elabExp (EnvML.Rec [])      = Left "Empty records not allowed."
elabExp (EnvML.Rec [(n, e)])= Core.Rec n <$> elabExp e
elabExp (EnvML.Rec fields) = do
  fields' <- traverse elabField fields
  pure $ Core.FEnv fields'
  where
    elabField (x, e) = Core.ExpE . Core.Rec x <$> elabExp e
elabExp (EnvML.RProj e l)   = Core.RProj <$> elabExp e <*> pure l
elabExp (EnvML.FEnv env)    = Core.FEnv <$> elabEnv env
elabExp (EnvML.Anno e ty)   = Core.Anno <$> elabExp e <*> elabTyp ty
elabExp (EnvML.ModE m)      = elabM m
elabExp (EnvML.BinOp op)    = case op of
  EnvML.Add e1 e2 -> fmap Core.BinOp (Core.Add <$> elabExp e1 <*> elabExp e2)
  EnvML.Sub e1 e2 -> fmap Core.BinOp (Core.Sub <$> elabExp e1 <*> elabExp e2)
  EnvML.Mul e1 e2 -> fmap Core.BinOp (Core.Mul <$> elabExp e1 <*> elabExp e2)
