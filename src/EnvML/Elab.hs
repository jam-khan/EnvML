{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module EnvML.Elab where

import qualified CoreFE.Named as CoreFE
import qualified EnvML.Syntax as EnvML

elabModule :: EnvML.Module -> CoreFE.Exp
elabModule = elabModuleExp

elabModuleExp ::
  EnvML.Module ->
  CoreFE.Exp
elabModuleExp modl =
  case modl of
    EnvML.VarM name -> CoreFE.Var name
    EnvML.Functor args m -> elabFunctor args m
    EnvML.Struct structs ->
      CoreFE.FEnv $ elabStructures structs
    EnvML.MApp m1 m2 ->
      CoreFE.App (elabModuleExp m1) (elabModuleExp m2)
    EnvML.MAppt m1 a ->
      CoreFE.TApp (elabModuleExp m1) (elabTyp a)
    EnvML.MAnno m mty ->
      CoreFE.Anno (elabModuleExp m) (elabModTyp mty)

-- Functors elaboration
elabFunctor :: EnvML.FunArgs -> EnvML.Module -> CoreFE.Exp
elabFunctor [] body = elabModuleExp body
elabFunctor ((name, arg) : rest) body =
  let restExp = elabFunctor rest body
   in case arg of
        EnvML.TyArg -> CoreFE.TLam name restExp
        EnvML.TmArg -> CoreFE.Lam name restExp
        EnvML.TmArgType _ ->
          -- NOTE: We ignore type annotations on parameters for now
          CoreFE.Lam name restExp

-- Structures elaboration
elabStructures :: EnvML.Structures -> CoreFE.Env
elabStructures = reverse . map elabStructure

-- Structure elaboration
elabStructure :: EnvML.Structure -> CoreFE.EnvE
elabStructure struct =
  case struct of
    (EnvML.Let name maybeTyp e) ->
      case maybeTyp of
        Nothing -> CoreFE.ModE name (elabExp e)
        Just ty -> CoreFE.ModE name (CoreFE.Anno (elabExp e) (elabTyp ty))
    (EnvML.TypDecl name ty) ->
      CoreFE.TypE name (elabTypWithBinder (Just name) ty)
    (EnvML.ModTypDecl name mty) ->
      CoreFE.TypE name (elabModTyp mty)
    (EnvML.ModStruct name maybeTyp mod1) ->
      case maybeTyp of
        Nothing -> CoreFE.ModE name (elabModuleExp mod1)
        Just mty -> CoreFE.ModE name (CoreFE.Anno (elabModuleExp mod1) (elabModTyp mty))
    (EnvML.FunctStruct name args maybeTyp mod1) ->
      case maybeTyp of
        Nothing -> CoreFE.ModE name (elabFunctor args mod1)
        Just mty -> CoreFE.ModE name (CoreFE.Anno (elabFunctor args mod1) (elabModTyp mty))

elabExp :: EnvML.Exp -> CoreFE.Exp
elabExp e =
  case e of
    (EnvML.Lit i) -> CoreFE.Lit i
    (EnvML.Var n) -> CoreFE.Var n
    (EnvML.Fix n e1) -> CoreFE.Fix n (elabExp e1)
    (EnvML.If e1 e2 e3) -> CoreFE.If (elabExp e1) (elabExp e2) (elabExp e3)
    (EnvML.Lam args e1) ->
      elabLambda args e1
    (EnvML.TLam _ _) ->
      error "Typed lambdas don't exist at source separately."
    (EnvML.Clos env args e1) ->
      let env' = elabEnv env
          body' = elabLambda args e1
       in CoreFE.Clos env' body'
    (EnvML.App e1 e2) -> CoreFE.App (elabExp e1) (elabExp e2)
    (EnvML.TClos {}) ->
      error "Typed closures don't exist at source separately."
    (EnvML.TApp e1 t) ->
      CoreFE.TApp (elabExp e1) (elabTyp t)
    (EnvML.Box env e1) ->
      CoreFE.Box (elabEnv env) (elabExp e1)
    (EnvML.Rec records) ->
      CoreFE.FEnv $ map (CoreFE.ExpE "_") $ elabRecords records
    (EnvML.RProj e1 n) ->
      CoreFE.RProj (elabExp e1) n
    (EnvML.FEnv env) ->
      CoreFE.FEnv (elabEnv env)
    (EnvML.Anno e1 ty) ->
      CoreFE.Anno (elabExp e1) (elabTyp ty)
    (EnvML.Mod m) -> elabModuleExp m
    (EnvML.DataCon ctor arg ty) ->
      let ty' = elabTyp ty
       in CoreFE.Fold ty' (CoreFE.DataCon ctor (elabExp arg))
    (EnvML.Case scrutinee branches) ->
      CoreFE.Case (CoreFE.Unfold (elabExp scrutinee)) (map elabCaseBranch branches)
    (EnvML.BinOp (EnvML.Add e1 e2)) ->
      CoreFE.BinOp (CoreFE.Add (elabExp e1) (elabExp e2))
    (EnvML.BinOp (EnvML.Sub e1 e2)) ->
      CoreFE.BinOp (CoreFE.Sub (elabExp e1) (elabExp e2))
    (EnvML.BinOp (EnvML.Mul e1 e2)) ->
      CoreFE.BinOp (CoreFE.Mul (elabExp e1) (elabExp e2))
    (EnvML.BinOp (EnvML.EqEq e1 e2)) ->
      CoreFE.BinOp (CoreFE.EqEq (elabExp e1) (elabExp e2))
    (EnvML.BinOp (EnvML.Neq e1 e2)) ->
      CoreFE.BinOp (CoreFE.Neq (elabExp e1) (elabExp e2))
    (EnvML.BinOp (EnvML.Lt e1 e2)) ->
      CoreFE.BinOp (CoreFE.Lt (elabExp e1) (elabExp e2))
    (EnvML.BinOp (EnvML.Le e1 e2)) ->
      CoreFE.BinOp (CoreFE.Le (elabExp e1) (elabExp e2))
    (EnvML.BinOp (EnvML.Gt e1 e2)) ->
      CoreFE.BinOp (CoreFE.Gt (elabExp e1) (elabExp e2))
    (EnvML.BinOp (EnvML.Ge e1 e2)) ->
      CoreFE.BinOp (CoreFE.Ge (elabExp e1) (elabExp e2))
    (EnvML.EList es) -> CoreFE.EList (map elabExp es)
    (EnvML.ETake i e1) -> CoreFE.ETake i (elabExp e1)

elabLambda :: EnvML.FunArgs -> EnvML.Exp -> CoreFE.Exp
elabLambda [] body = elabExp body
elabLambda ((name, arg) : rest) body =
  let restExp = elabLambda rest body
   in case arg of
        EnvML.TyArg -> CoreFE.TLam name restExp
        EnvML.TmArg -> CoreFE.Lam name restExp
        EnvML.TmArgType _ ->
          -- NOTE: Ignoring type parameters for now
          CoreFE.Lam name restExp

elabRecords :: [(EnvML.Name, EnvML.Exp)] -> [CoreFE.Exp]
elabRecords [] = []
elabRecords ((n, e) : rest) =
  CoreFE.Rec n (elabExp e) : elabRecords rest

elabEnv :: EnvML.Env -> CoreFE.Env
elabEnv = reverse . map elabEnvE

elabEnvE :: EnvML.EnvE -> CoreFE.EnvE
elabEnvE envE =
  case envE of
    (EnvML.ExpEN name e) -> CoreFE.ExpE name (elabExp e)
    (EnvML.ExpE e) -> CoreFE.ExpE "_" (elabExp e)
    (EnvML.TypEN name ty) -> CoreFE.TypE name (elabTyp ty)
    (EnvML.TypE ty) -> CoreFE.TypE "_" (elabTyp ty)
    (EnvML.ModE name m) -> CoreFE.ModE name (elabModule m)
    (EnvML.ModTypE name mty) -> CoreFE.TypE name (elabModTyp mty)

elabTyp :: EnvML.Typ -> CoreFE.Typ
elabTyp = elabTypWithBinder Nothing

elabTypWithBinder :: Maybe EnvML.Name -> EnvML.Typ -> CoreFE.Typ
elabTypWithBinder maybeBinder ty =
  case ty of
    (EnvML.TyLit lit) -> CoreFE.TyLit lit
    (EnvML.TyVar n) -> CoreFE.TyVar n
    (EnvML.TyArr ta tb) -> CoreFE.TyArr (elabTypWithBinder maybeBinder ta) (elabTypWithBinder maybeBinder tb)
    (EnvML.TyAll n ty1) -> CoreFE.TyAll n (elabTypWithBinder maybeBinder ty1)
    (EnvML.TyBoxT ctx ty1) -> CoreFE.TyBoxT (elabTyCtx ctx) (elabTypWithBinder maybeBinder ty1)
    (EnvML.TyRcd fields) -> CoreFE.TyEnvt $ map (CoreFE.Type "_") $ elabRcdFieldsTy fields
    (EnvML.TySum ctors) ->
      let binder = case maybeBinder of
            Just n -> n
            Nothing -> error "Sum types must be declared with a binder"
          ctors' = [(name, elabTypWithBinder maybeBinder payloadTy) | (name, payloadTy) <- ctors]
       in CoreFE.TyMu binder (CoreFE.TySum ctors')
    (EnvML.TyCtx ctx) -> CoreFE.TyEnvt (elabTyCtx ctx)
    (EnvML.TyModule mty) -> elabModTyp mty
    (EnvML.TyList ty1) -> CoreFE.TyList $ elabTypWithBinder maybeBinder ty1

elabTyCtx :: EnvML.TyCtx -> CoreFE.TyEnv
elabTyCtx = reverse . map elabTyCtxE

elabTyCtxE :: EnvML.TyCtxE -> CoreFE.TyEnvE
elabTyCtxE ctxE =
  case ctxE of
    (EnvML.TypeN name ty) ->
      CoreFE.Type name (elabTyp ty)
    (EnvML.Type ty) ->
      CoreFE.Type "_" (elabTyp ty)
    (EnvML.KindN name) -> CoreFE.Kind name
    EnvML.Kind -> CoreFE.Kind "_"
    (EnvML.TypeEqN name ty) ->
      CoreFE.TypeEq name (elabTyp ty)
    (EnvML.TyMod name mty) ->
      CoreFE.Type name (elabModTyp mty)
    (EnvML.TypeEqM name mty) ->
      CoreFE.TypeEq name (elabModTyp mty)

elabRcdFieldsTy :: [(EnvML.Name, EnvML.Typ)] -> [CoreFE.Typ]
elabRcdFieldsTy [] = []
elabRcdFieldsTy ((n, ty) : rest) =
  CoreFE.TyRcd n (elabTyp ty) : elabRcdFieldsTy rest

elabCaseBranch :: EnvML.CaseBranch -> CoreFE.CaseBranch
elabCaseBranch (EnvML.CaseBranch ctor binder body) =
  CoreFE.CaseBranch ctor binder (elabExp body)

elabModTyp :: EnvML.ModuleTyp -> CoreFE.Typ
elabModTyp mty =
  case mty of
    (EnvML.TyArrowM ty mty1) ->
      CoreFE.TyArr (elabTyp ty) (elabModTyp mty1)
    (EnvML.ForallM n mty1) ->
      CoreFE.TyAll n (elabModTyp mty1)
    (EnvML.TySig intf) ->
      CoreFE.TyEnvt (elabIntf intf)
    (EnvML.TyVarM name) ->
      CoreFE.TyVar name

elabIntf :: EnvML.Intf -> CoreFE.TyEnv
elabIntf = reverse . map elabIntfE

elabIntfE :: EnvML.IntfE -> CoreFE.TyEnvE
elabIntfE intfE =
  case intfE of
    (EnvML.TyDef name ty) ->
      CoreFE.TypeEq name (elabTyp ty)
    (EnvML.ValDecl name ty) ->
      CoreFE.Type name (CoreFE.TyRcd name (elabTyp ty))
    (EnvML.ModDecl name ty) ->
      CoreFE.Type name (CoreFE.TyRcd name (elabTyp ty))
    (EnvML.FunctorDecl name args retTyp) ->
      CoreFE.TypeEq name (elabFunctorDeclToType args retTyp)
    (EnvML.SigDecl name intf) ->
      CoreFE.TypeEq name (CoreFE.TyEnvt (elabIntf intf))

elabFunctorDeclToType :: EnvML.FunArgs -> EnvML.Typ -> CoreFE.Typ
elabFunctorDeclToType [] retTyp = elabTyp retTyp
elabFunctorDeclToType ((name, arg) : rest) retTyp =
  let restType = elabFunctorDeclToType rest retTyp
   in case arg of
        EnvML.TyArg ->
          CoreFE.TyAll name restType
        EnvML.TmArg ->
          error $ "Functor argument '" ++ name ++ "' must have type annotation"
        EnvML.TmArgType ty ->
          CoreFE.TyArr (elabTyp ty) restType