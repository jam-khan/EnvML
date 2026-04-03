module EnvML.Desugar (desugarModule, desugarExp) where

import qualified EnvML.Syntax as Src
import qualified EnvML.Desugared as D

desugarModule :: Src.Module -> D.Module
desugarModule m = case m of
  Src.VarM n      -> D.VarM n
  Src.Functor as b -> desugarFunctor as b
  Src.Struct ss   -> D.Struct (reverse $ map desugarStructure ss)
  Src.MApp m1 m2  -> D.MApp (desugarModule m1) (desugarModule m2)
  Src.MAppt m1 t  -> D.MAppt (desugarModule m1) t
  Src.MAnno m1 mt -> D.MAnno (desugarModule m1) mt

-- | Multi-arg functor → nested single-arg functors
desugarFunctor :: Src.FunArgs -> Src.Module -> D.Module
desugarFunctor [] body = desugarModule body
desugarFunctor ((name, arg) : rest) body =
  D.Functor name arg (desugarFunctor rest body)

desugarStructure :: Src.Structure -> D.Structure
desugarStructure s = case s of
  Src.Let n mt e          -> D.Let n (fmap desugarTyp mt) (desugarExp e)
  Src.TypDecl n t         -> D.TypDecl n (desugarTypWithBinder (Just n) t)
  Src.ModTypDecl n mt     -> D.ModTypDecl n mt
  Src.ModStruct n mt m    -> D.ModStruct n mt (desugarModule m)
  -- FunctStruct desugars into ModStruct with nested Functor body
  Src.FunctStruct n as mt m -> D.ModStruct n mt (desugarFunctor as m)

desugarExp :: Src.Exp -> D.Exp
desugarExp e = case e of
  Src.Lit l         -> D.Lit l
  Src.Var n         -> D.Var n
  Src.Fix n e1      -> D.Fix n (desugarExp e1)
  Src.If c t f      -> D.If (desugarExp c) (desugarExp t) (desugarExp f)
  -- Multi-arg lambdas → nested single-arg
  Src.Lam as body   -> desugarLambda as body
  Src.Clos env as body -> D.Clos (desugarEnv env) (desugarLambda as body)
  Src.App e1 e2     -> D.App (desugarExp e1) (desugarExp e2)
  Src.TClos env as body -> D.TClos (desugarEnv env) (desugarLambda as body)
  Src.TApp e1 t     -> D.TApp (desugarExp e1) t
  Src.Box env e1    -> D.Box (desugarEnv env) (desugarExp e1)
  Src.Rec fs        -> D.Rec [(n, desugarExp v) | (n, v) <- fs]
  Src.RProj e1 n    -> D.RProj (desugarExp e1) n
  Src.FEnv env      -> D.FEnv (desugarEnv env)
  Src.Anno e1 t     -> D.Anno (desugarExp e1) t
  Src.Mod m         -> D.Mod (desugarModule m)
  -- Wrap constructor with fold
  Src.DataCon ctor arg ty -> D.Fold ty (D.DataCon ctor (desugarExp arg) ty)
  -- Wrap case scrutinee with unfold
  Src.Case scrut bs -> D.Case (D.Unfold (desugarExp scrut)) (map desugarBranch bs)
  Src.Fold t e1     -> D.Fold t (desugarExp e1)
  Src.Unfold e1     -> D.Unfold (desugarExp e1)
  Src.EList es      -> D.EList (map desugarExp es)
  Src.ETake i e1    -> D.ETake i (desugarExp e1)
  Src.BinOp op      -> D.BinOp (desugarBinOp op)

-- | Multi-arg lambda → nested single-arg Lam/TLam
desugarLambda :: Src.FunArgs -> Src.Exp -> D.Exp
desugarLambda [] body = desugarExp body
desugarLambda ((name, arg) : rest) body =
  case arg of
    Src.TyArg       -> D.TLam name (desugarLambda rest body)
    Src.TmArg       -> D.Lam name Nothing (desugarLambda rest body)
    Src.TmArgType t -> D.Lam name (Just (desugarTyp t)) (desugarLambda rest body)

desugarBranch :: Src.CaseBranch -> D.CaseBranch
desugarBranch (Src.CaseBranch ctor binder body) =
  D.CaseBranch ctor binder (desugarExp body)

desugarBinOp :: Src.BinOp -> D.BinOp
desugarBinOp op = case op of
  Src.Add e1 e2  -> D.Add (desugarExp e1) (desugarExp e2)
  Src.Sub e1 e2  -> D.Sub (desugarExp e1) (desugarExp e2)
  Src.Mul e1 e2  -> D.Mul (desugarExp e1) (desugarExp e2)
  Src.EqEq e1 e2 -> D.EqEq (desugarExp e1) (desugarExp e2)
  Src.Neq e1 e2  -> D.Neq (desugarExp e1) (desugarExp e2)
  Src.Lt e1 e2   -> D.Lt (desugarExp e1) (desugarExp e2)
  Src.Le e1 e2   -> D.Le (desugarExp e1) (desugarExp e2)
  Src.Gt e1 e2   -> D.Gt (desugarExp e1) (desugarExp e2)
  Src.Ge e1 e2   -> D.Ge (desugarExp e1) (desugarExp e2)

desugarEnv :: Src.Env -> D.Env
desugarEnv = reverse . map desugarEnvE

desugarEnvE :: Src.EnvE -> D.EnvE
desugarEnvE envE = case envE of
  Src.ExpEN n e   -> D.ExpEN n (desugarExp e)
  Src.ExpE e      -> D.ExpE (desugarExp e)
  Src.TypEN n t   -> D.TypEN n (desugarTyp t)
  Src.TypE t      -> D.TypE (desugarTyp t)
  Src.ModE n m    -> D.ModE n (desugarModule m)
  Src.ModTypE n t -> D.ModTypE n t

desugarTyp :: Src.Typ -> Src.Typ
desugarTyp = desugarTypWithBinder Nothing

desugarTypWithBinder :: Maybe Src.Name -> Src.Typ -> Src.Typ
desugarTypWithBinder mb ty = case ty of
  Src.TyLit l      -> Src.TyLit l
  Src.TyVar n      -> Src.TyVar n
  Src.TyArr a b    -> Src.TyArr (desugarTypWithBinder mb a) (desugarTypWithBinder mb b)
  Src.TyAll n t    -> Src.TyAll n (desugarTypWithBinder mb t)
  Src.TyBoxT ctx t -> Src.TyBoxT (reverse ctx) (desugarTypWithBinder mb t)
  Src.TyRcd fs     -> Src.TyRcd [(n, desugarTypWithBinder mb t) | (n, t) <- fs]
  Src.TySum ctors  ->
    let ctors' = [(n, desugarTypWithBinder mb t) | (n, t) <- ctors]
    in case mb of
      Just binder -> Src.TyMu binder (Src.TySum ctors')
      Nothing     -> Src.TySum ctors'
  Src.TyMu n t     -> Src.TyMu n (desugarTypWithBinder (Just n) t)
  Src.TyCtx ctx    -> Src.TyCtx (reverse ctx)
  Src.TyModule mt  -> Src.TyModule mt
  Src.TyList t     -> Src.TyList (desugarTypWithBinder mb t)
