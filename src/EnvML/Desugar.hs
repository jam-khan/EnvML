module EnvML.Desugar where

import EnvML.Parser.AST as N

desugarExp :: N.Exp -> N.Exp
desugarExp e = case e of
  N.Lit l    -> N.Lit l
  N.Var x    -> N.Var x
  
  N.Lam [] _ ->
    error $ "Parse error: Functions must have arguments.\n" ++ pretty e
  
  -- Single arg lambdas - distinguish type vs term
  N.Lam [(x, TyArg)] body ->
    N.TLam [(x, TyArg)] $ desugarExp body
  
  N.Lam [(x, TmArg)] body ->
    N.Lam [(x, TmArg)] $ desugarExp body
  
  N.Lam [(x, TmArgType t)] body ->
    N.Lam [(x, TmArgType (desugarTyp t))] $ desugarExp body
  
  -- Multi-arg lambdas
  N.Lam ((x, arg) : rest) body ->
    case arg of
      TyArg ->
        N.TLam [(x, arg)] $ desugarExp (N.Lam rest body)
      TmArg ->
        N.Lam [(x, arg)] $ desugarExp (N.Lam rest body)
      TmArgType t ->
        N.Lam [(x, TmArgType (desugarTyp t))] $ desugarExp (N.Lam rest body)
  
  -- TLam - handle for idempotence
  N.TLam [(x, TyArg)] body ->
    N.TLam [(x, TyArg)] (desugarExp body)
  
  N.TLam _ _ ->
    error "Multi-arg TLam should be desugared already!"
  
  -- Closures
  N.Clos env args body ->
    N.Clos (desugarEnv env) [] $ desugarExp (N.Lam args body)
  
  N.TClos env args body ->
    N.TClos (desugarEnv env) [] $ desugarExp (N.Lam args body)
  
  -- Applications
  N.App e1 e2 ->
    N.App (desugarExp e1) (desugarExp e2)
  
  N.TApp e1 t ->
    N.TApp (desugarExp e1) (desugarTyp t)
  
  -- Box
  N.Box env e1 ->
    N.Box (desugarEnv env) (desugarExp e1)
  
  -- Records
  N.Rec [] ->
    error "Parse error: Empty record not allowed."
  
  N.Rec fields ->
    N.Rec (map (\(n, e1) -> (n, desugarExp e1)) fields)
  
  N.RProj e1 x ->
    N.RProj (desugarExp e1) x
  
  -- Environment
  N.FEnv env ->
    N.FEnv $ desugarEnv env
  
  -- Annotation
  N.Anno e1 t ->
    N.Anno (desugarExp e1) (desugarTyp t)
  
  -- Module
  N.Mod m ->
    N.Mod $ desugarModule m
  
  -- Binary operations
  N.BinOp op ->
    N.BinOp $ desugarBinOp op

desugarModule :: N.Module -> N.Module
desugarModule m = case m of
  -- Empty functor args - just desugar body
  N.Functor [] body ->
    desugarModule body
  
  -- Single-arg functor - keep it
  N.Functor [(n, arg)] body ->
    N.Functor [(n, arg)] (desugarModule body)
  
  -- Multi-arg functor - desugar to nested
  N.Functor ((n, arg) : rest) body ->
    N.Functor [(n, arg)] (desugarModule (N.Functor rest body))
  
  N.VarM x ->
    N.VarM x
  
  N.Struct imps env ->
    N.Struct imps (desugarEnv env)
  
  N.MApp m1 m2 ->
    N.MApp (desugarModule m1) (desugarModule m2)
  
  N.MAppt m1 t ->
    N.MAppt (desugarModule m1) (desugarTyp t)
  
  N.MLink m1 m2 ->
    N.MLink (desugarModule m1) (desugarModule m2)

desugarBinOp :: N.BinOp -> N.BinOp
desugarBinOp op = case op of
  N.Add e1 e2 -> N.Add (desugarExp e1) (desugarExp e2)
  N.Sub e1 e2 -> N.Sub (desugarExp e1) (desugarExp e2)
  N.Mul e1 e2 -> N.Mul (desugarExp e1) (desugarExp e2)

desugarEnv :: N.Env -> N.Env
desugarEnv = map desugarEnvE

desugarEnvE :: N.EnvE -> N.EnvE
desugarEnvE e = case e of
  N.ExpEN n ex    -> N.ExpEN n (desugarExp ex)
  N.ExpE ex       -> N.ExpE (desugarExp ex)
  N.TypEN n t     -> N.TypEN n (desugarTyp t)
  N.TypE t        -> N.TypE (desugarTyp t)
  N.ModE n m      -> N.ModE n (desugarModule m)
  N.ModTypE n mt  -> N.ModTypE n (desugarModuleTyp mt)

desugarModuleTyp :: N.ModuleTyp -> N.ModuleTyp
desugarModuleTyp mt = case mt of
  N.TyArrowM t mt1  -> N.TyArrowM (desugarTyp t) (desugarModuleTyp mt1)
  N.TySig intf      -> N.TySig (desugarIntf intf)
  N.ForallM n intf  -> N.ForallM n $ desugarModuleTyp intf

desugarIntf :: N.Intf -> N.Intf
desugarIntf = map desugarIntfE

desugarIntfE :: N.IntfE -> N.IntfE
desugarIntfE ie = case ie of
  N.TyDef n t -> N.TyDef n (desugarTyp t)
  N.ValDecl n t -> N.ValDecl n (desugarTyp t)
  N.ModDecl n s -> N.ModDecl n (desugarModuleTyp s)
  
  N.FunctorDecl name [] _ ->
    error $ "Parser error: Functor `" ++ name ++ "` must have at least one argument."
  
  N.FunctorDecl name args mt ->
    N.ModDecl name (desugarFunctorDeclToType args mt)
  
  N.SigDecl n mt -> N.SigDecl n (desugarIntf mt)

desugarFunctorDeclToType :: FunArgs -> N.ModuleTyp -> N.ModuleTyp
desugarFunctorDeclToType [] mt = desugarModuleTyp mt
desugarFunctorDeclToType ((name, arg):rest) mt =
  let restType = desugarFunctorDeclToType rest mt
  in case arg of
    N.TyArg ->
      N.ForallM name restType
    N.TmArg ->
      error $ "Functor argument '" ++ name ++ "' must have type annotation."
    N.TmArgType t ->
      N.TyArrowM (desugarTyp t) restType

desugarTyp :: N.Typ -> N.Typ
desugarTyp t = case t of
  N.TyLit l -> N.TyLit l
  N.TyVar n -> N.TyVar n
  N.TyArr t1 t2 -> N.TyArr (desugarTyp t1) (desugarTyp t2)
  N.TyAll n t1 -> N.TyAll n $ desugarTyp t1
  N.TyBoxT g ty -> N.TyBoxT (desugarTyCtx g) (desugarTyp ty)
  
  N.TyRcd [] ->
    error $ "Parse error: Empty record type not allowed" ++ pretty t
  
  N.TyRcd fields ->
    N.TyRcd (map (\(n, ty) -> (n, desugarTyp ty)) fields)
  
  N.TyCtx ctx -> N.TyCtx $ desugarTyCtx ctx
  N.TyModule mt -> N.TyModule (desugarModuleTyp mt)

desugarTyCtx :: N.TyCtx -> N.TyCtx
desugarTyCtx = map desugarTyCtxE

desugarTyCtxE :: N.TyCtxE -> N.TyCtxE
desugarTyCtxE a = case a of
  N.TypeN name ty    -> N.TypeN name  $ desugarTyp ty
  N.Type  ty         -> N.Type $ desugarTyp ty
  N.KindN name       -> N.KindN name
  N.Kind             -> N.Kind
  N.TypeEqN name typ -> N.TypeEqN name $ desugarTyp typ
  N.TyMod   name mty -> N.TyMod   name $ desugarModuleTyp mty
  N.TypeEqM name mty -> N.TypeEqM name $ desugarModuleTyp mty