{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant where" #-}
module EnvML.Parser.ElabAST (elabExp, elabTyp, elabIntf, elabModule, elabModuleTyp) where

-- Named AST
-- De-bruijn AST

import Data.List (elemIndex)
import qualified EnvML.Parser.AST as N
import qualified EnvML.Syntax as D

type Ctx = [N.Name]

lookupVar :: N.Name -> Ctx -> Int
lookupVar x ctx =
  case elemIndex x ctx of
    Just i -> i
    Nothing -> error $ "Unbound type variable: " ++ x

getName :: N.IntfE -> N.Name
getName ie =
  case ie of
    N.TyDef n _ -> n
    N.ValDecl n _ -> n
    N.ModDecl n _ -> n
    N.SigDecl n _ -> n

-- All user-given type environments are reversed from this phase on
elabTyEnv :: Ctx -> N.TyEnv -> D.TyEnv
elabTyEnv ctx env = reverse $ elabTyEnv' ctx env
  where
    elabTyEnv' _ [] = []
    elabTyEnv' ctx' ((n, e) : es) = elabTyEnvE ctx' e : elabTyEnv' (n : ctx') es

elabTyp :: Ctx -> N.Typ -> D.Typ
elabTyp ctx t = case t of
  N.TyLit l -> D.TyLit (elabLitTyp l)
  N.TyVar n -> D.TyVar (lookupVar n ctx)
  N.TyArr t1 t2 -> D.TyArr (elabTyp ctx t1) (elabTyp ctx t2)
  N.TyAll n t1 -> D.TyAll (elabTyp (n : ctx) t1)
  -- TyBoxT: [t1:A, t2:B] t1 -> t2 ~~> TyBoxT [A, B] _1_ -> _0_
  -- We elaborate the environment entries in the current context.
  -- Then we extend the context for T. We reverse the names so the
  -- last one in the list (t2) is at the head (index 0).
  N.TyBoxT env t1 ->
    let g = map (\(_, e) -> elabTyEnvE ctx e) env
        gNames = reverse (map fst env)
     in D.TyBoxT g (elabTyp gNames t1)
  -- TySubstT: [x:=A] b
  N.TyRcd s t1 -> D.TyRcd s (elabTyp ctx t1)
  N.TyEnvt env -> D.TyEnvt (elabTyEnv ctx env)
  N.TyModule mt -> D.TyModule (elabModuleTyp ctx mt)

elabTyEnvE :: Ctx -> N.TyEnvE -> D.TyEnvE
elabTyEnvE ctx e = case e of
  N.Type t -> D.Type (elabTyp ctx t)
  N.Kind -> D.Kind
  N.TypeEq t -> D.TypeEq (elabTyp ctx t)

elabModuleTyp :: Ctx -> N.ModuleTyp -> D.ModuleTyp
elabModuleTyp ctx mt = case mt of
  N.TyArrowM t mt1 -> D.TyArrowM (elabTyp ctx t) (elabModuleTyp ctx mt1)
  N.TySig intf -> D.TySig (elabIntf ctx intf)

-- All user-given type interfaces are reversed from this phase on
elabIntf :: Ctx -> N.Intf -> D.Intf
elabIntf ctx intf = reverse $ elabIntf' ctx intf
  where
    elabIntf' _ [] = []
    elabIntf' ctx' (x : xs) = elabIntfE ctx' x : elabIntf' (getName x : ctx') xs

elabIntfE :: Ctx -> N.IntfE -> D.IntfE
elabIntfE ctx ie = case ie of
  N.TyDef _ t -> D.TyDef (elabTyp ctx t)
  N.ValDecl _ t -> D.ValDecl (elabTyp ctx t)
  N.ModDecl _ s -> D.ModDecl (D.TyVar $ lookupVar s ctx)
  N.SigDecl _ mt -> D.SigDecl (elabModuleTyp ctx mt)

elabLitTyp :: N.TyLit -> D.TyLit
elabLitTyp N.TyInt = D.TyInt
elabLitTyp N.TyBool = D.TyBool
elabLitTyp N.TyStr = D.TyStr

-- All user-given environments are reversed from this phase on
elabEnv :: Ctx -> N.Env -> D.Env
elabEnv ctx env = reverse $ elabEnv' ctx env
  where
    elabEnv' _ [] = []
    elabEnv' ctx' ((n, e) : es) = elabEnvE ctx' e : elabEnv' (n : ctx') es

elabEnvE :: Ctx -> N.EnvE -> D.EnvE
elabEnvE ctx e =
  case e of
    N.ExpE ex -> D.ExpE (elabExp ctx ex)
    N.TypE t -> D.TypE (elabTyp ctx t)

elabModule :: Ctx -> N.Module -> D.Module
elabModule ctx (N.Functor n t m) =
  D.Functor (elabTyp ctx t) (elabModule (n : ctx) m)
elabModule ctx (N.Struct imps env) =
    let binds = map fst imps
        ctx' = reverse binds ++ ctx
        structMod = D.Struct (elabEnv ctx' env)
    in
    foldr (\(_, t) modl -> D.Functor (elabTyp ctx t) modl) structMod imps
elabModule ctx (N.MApp m1 m2) =
  D.MApp (elabModule ctx m1) (elabModule ctx m2)
elabModule ctx (N.MLink m1 m2) =
  D.MLink (elabModule ctx m1) (elabModule ctx m2)

elabExp :: Ctx -> N.Exp -> D.Exp
elabExp _ (N.Lit l) =
  case l of
    N.LitInt n -> D.Lit (D.LitInt n)
    N.LitBool b -> D.Lit (D.LitBool b)
    N.LitStr s -> D.Lit (D.LitStr s)
elabExp ctx (N.Var x) = D.Var (lookupVar x ctx)
elabExp ctx (N.Lam a e) =
  D.Lam (elabExp (a : ctx) e)
elabExp ctx (N.Clos env a e) =
  D.Clos (elabEnv ctx env) (elabExp (a : ctx) e)
elabExp ctx (N.App e1 e2) =
  D.App (elabExp ctx e1) (elabExp ctx e2)
elabExp ctx (N.TLam a e) =
  D.TLam (elabExp (a : ctx) e)
elabExp ctx (N.TClos env a e) =
  D.TClos (elabEnv ctx env) (elabExp (a : ctx) e)
elabExp ctx (N.TApp e t) =
  D.TApp (elabExp ctx e) (elabTyp ctx t)
elabExp ctx (N.Box env e) =
  let boxenv = map fst env
   in D.Box (elabEnv ctx env) (elabExp boxenv e)
elabExp ctx (N.Rec l e) =
  D.Rec l (elabExp ctx e)
elabExp ctx (N.RProj e a) =
  D.RProj (elabExp ctx e) a
elabExp ctx (N.FEnv env) =
  D.FEnv (elabEnv ctx env)
elabExp ctx (N.Anno e t) =
  D.Anno (elabExp ctx e) (elabTyp ctx t)
elabExp ctx (N.ModE m) =
  D.ModE (elabModule ctx m)
