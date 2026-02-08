{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module EnvML.Elab where

import qualified Core.Named         as Core
import qualified EnvML.Syntax   as EnvML

type ElabError = String


elabModule :: EnvML.Module -> Core.Exp
elabModule = elabModuleExp

elabModuleExp :: 
  EnvML.Module 
  -> Core.Exp
elabModuleExp modl =
  case modl of
    EnvML.VarM name         -> Core.Var name
    EnvML.Functor args m    -> elabFunctor args m
    EnvML.Struct structs    ->
      Core.FEnv $ elabStructures structs
    EnvML.MApp m1 m2        ->
      Core.App (elabModuleExp m1) (elabModuleExp m2)
    EnvML.MAppt m1 a        ->
      Core.TApp (elabModuleExp m1) (elabTyp a)
    EnvML.MAnno m mty       ->
      Core.Anno (elabModuleExp m) (elabModTyp mty)
  

-- Functors elaboration
elabFunctor :: EnvML.FunArgs -> EnvML.Module -> Core.Exp
elabFunctor [] body = elabModuleExp body
elabFunctor ((name, arg):rest) body =
  let restExp = elabFunctor rest body
  in  case arg of
        EnvML.TyArg -> Core.TLam name restExp
        EnvML.TmArg -> Core.Lam  name restExp
        EnvML.TmArgType _ ->
          -- NOTE: We ignore type annotations on parameters for now
          Core.Lam name restExp

-- Structures elaboration
elabStructures :: EnvML.Structures -> Core.Env
elabStructures = map elabStructure

-- Structure elaboration
elabStructure :: EnvML.Structure -> Core.EnvE
elabStructure struct =
  case struct of
    (EnvML.Let name maybeTyp e)           ->
      case maybeTyp of
        Nothing -> Core.ModE name (elabExp e)
        Just ty -> Core.ModE name (Core.Anno (elabExp e) (elabTyp ty))
    (EnvML.TypDecl name ty)               ->
      Core.TypE name (elabTyp ty)
    (EnvML.ModTypDecl name mty)           ->
      Core.TypE name (elabModTyp mty)
    (EnvML.ModStruct name maybeTyp mod1)  ->
      case maybeTyp of
        Nothing   -> Core.ModE name (elabModuleExp mod1)
        Just mty  -> Core.ModE name (Core.Anno (elabModuleExp mod1) (elabModTyp mty))       
    (EnvML.FunctStruct name args maybeTyp mod1) ->
      case maybeTyp of
        Nothing   -> Core.ModE name (elabFunctor args mod1)
        Just mty  -> Core.ModE name (Core.Anno (elabFunctor args mod1) (elabModTyp mty))
  
elabExp :: EnvML.Exp -> Core.Exp
elabExp e = 
  case e of
    (EnvML.Lit i)           -> Core.Lit i
    (EnvML.Var n)           -> Core.Var n
    (EnvML.Lam args e1)     -> 
      elabLambda args e1
    (EnvML.TLam _ _)        -> 
      error "Typed lambdas don't exist at source separately."
    (EnvML.Clos env args e1)->
      let env'  = elabEnv env
          body' = elabLambda args e1
      in  Core.Clos env' body'
    (EnvML.App e1 e2)       -> Core.App (elabExp e1) (elabExp e2)
    (EnvML.TClos {})        -> 
      error "Typed closures don't exist at source separately."
    (EnvML.TApp e1 t)       ->
      Core.TApp (elabExp e1) (elabTyp t)
    (EnvML.Box env e1)      -> 
      Core.Box (elabEnv env) (elabExp e1)
    (EnvML.Rec records)     -> 
      Core.FEnv $ map (Core.ExpE "_") $ elabRecords records
    (EnvML.RProj e1 n)      -> 
      Core.RProj (elabExp e1) n
    (EnvML.FEnv env)        ->
      Core.FEnv (elabEnv env)
    (EnvML.Anno e1 ty)      ->
      Core.Anno (elabExp e1) (elabTyp ty)
    (EnvML.Mod m)           -> elabModuleExp m
    (EnvML.BinOp op)        ->
      error $ "TODO: Binary operators to be supported " ++ show op

elabLambda :: EnvML.FunArgs -> EnvML.Exp -> Core.Exp
elabLambda [] body = elabExp body
elabLambda ((name, arg):rest) body =
  let restExp = elabLambda rest body
  in  case arg of
        EnvML.TyArg -> Core.TLam name restExp
        EnvML.TmArg -> Core.Lam  name restExp
        EnvML.TmArgType _ ->
          -- NOTE: Ignoring type parameters for now
          Core.Lam name restExp

elabRecords :: [(EnvML.Name, EnvML.Exp)] -> [Core.Exp]
elabRecords []            = []
elabRecords ((n, e):rest) = 
  Core.Rec n (elabExp e):elabRecords rest

elabEnv :: EnvML.Env -> Core.Env
elabEnv = map elabEnvE

elabEnvE :: EnvML.EnvE -> Core.EnvE
elabEnvE envE = 
  case envE of
    (EnvML.ExpEN name e)    -> Core.ExpE name (elabExp e)
    (EnvML.ExpE e)          -> Core.ExpE "_" (elabExp e)
    (EnvML.TypEN name ty)   -> Core.TypE name (elabTyp ty)
    (EnvML.TypE ty)         -> Core.TypE "_" (elabTyp ty)
    (EnvML.ModE name m)     -> Core.ModE name (elabModule m)
    (EnvML.ModTypE name mty)-> Core.TypE name (elabModTyp mty)

elabTyp :: EnvML.Typ -> Core.Typ
elabTyp ty =
  case ty of
    (EnvML.TyLit lit)       -> Core.TyLit lit
    (EnvML.TyVar n)         -> Core.TyVar n
    (EnvML.TyArr ta tb)     -> Core.TyArr   (elabTyp ta) (elabTyp tb)
    (EnvML.TyAll n ty1)     -> Core.TyAll n (elabTyp ty1)
    (EnvML.TyBoxT ctx ty1)  -> Core.TyBoxT  (elabTyCtx ctx) (elabTyp ty1)
    (EnvML.TyRcd fields)    -> Core.TyEnvt $ map (Core.Type "_") $ elabRcdFieldsTy fields
    (EnvML.TyCtx ctx)       -> Core.TyEnvt  (elabTyCtx ctx)
    (EnvML.TyModule mty)    -> elabModTyp mty

elabTyCtx :: EnvML.TyCtx -> Core.TyEnv
elabTyCtx = map elabTyCtxE

elabTyCtxE :: EnvML.TyCtxE -> Core.TyEnvE
elabTyCtxE ctxE =
  case ctxE of
    (EnvML.TypeN name ty) ->
      Core.Type name (elabTyp ty)    
    (EnvML.Type ty) ->
      Core.Type "_" (elabTyp ty)    
    (EnvML.KindN name)  -> Core.Kind name
    EnvML.Kind          -> Core.Kind "_"
    (EnvML.TypeEqN name ty) ->
      Core.TypeEq name (elabTyp ty)    
    (EnvML.TyMod name mty) ->
      Core.Type name (elabModTyp mty)
    (EnvML.TypeEqM name mty) ->
      Core.TypeEq name (elabModTyp mty)

elabRcdFieldsTy :: [(EnvML.Name, EnvML.Typ)] -> [Core.Typ]
elabRcdFieldsTy []            = []
elabRcdFieldsTy ((n, ty):rest) =
  Core.TyRcd n (elabTyp ty):elabRcdFieldsTy rest
elabModTyp :: EnvML.ModuleTyp -> Core.Typ
elabModTyp mty =
  case mty of
    (EnvML.TyArrowM ty mty1)   -> 
      Core.TyArr (elabTyp ty) (elabModTyp mty1)
    (EnvML.ForallM n mty1)     ->
      Core.TyAll n (elabModTyp mty1)
    (EnvML.TySig intf)        ->
      Core.TyEnvt (elabIntf intf)
    (EnvML.TyVarM name)       ->
      Core.TyVar name

elabIntf :: EnvML.Intf -> Core.TyEnv
elabIntf = map elabIntfE

elabIntfE :: EnvML.IntfE -> Core.TyEnvE
elabIntfE intfE =
  case intfE of
    (EnvML.TyDef name ty) ->
      Core.TypeEq name (elabTyp ty)    
    (EnvML.ValDecl name ty) ->
      Core.Type name (Core.TyEnvt [Core.Type "_" (Core.TyRcd name (elabTyp ty))])
    (EnvML.ModDecl name ty) ->
      Core.Type name (Core.TyRcd name (elabTyp ty))    
    (EnvML.FunctorDecl name args retTyp) ->
      Core.TypeEq name (elabFunctorDeclToType args retTyp)
    (EnvML.SigDecl name intf) ->
      Core.TypeEq name (Core.TyEnvt (elabIntf intf))

elabFunctorDeclToType :: EnvML.FunArgs -> EnvML.Typ -> Core.Typ
elabFunctorDeclToType [] retTyp = elabTyp retTyp
elabFunctorDeclToType ((name, arg):rest) retTyp =
  let restType = elabFunctorDeclToType rest retTyp
  in  case arg of
        EnvML.TyArg ->
          Core.TyAll name restType
        EnvML.TmArg ->
          error $ "Functor argument '" ++ name ++ "' must have type annotation"
        EnvML.TmArgType ty ->
          Core.TyArr (elabTyp ty) restType