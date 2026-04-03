{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module EnvML.Elab where

import qualified CoreFE.Named as CoreFE
import qualified EnvML.Desugared as D
import qualified EnvML.Syntax as EnvML

elabModule :: D.Module -> CoreFE.Exp
elabModule = elabModuleExp

elabModuleExp :: D.Module -> CoreFE.Exp
elabModuleExp modl =
  case modl of
    D.VarM name -> CoreFE.Var name
    D.Functor name arg m ->
      case arg of
        EnvML.TyArg       -> CoreFE.TLam name (elabModuleExp m)
        EnvML.TmArg       -> CoreFE.Lam name (elabModuleExp m)
        EnvML.TmArgType _  -> CoreFE.Lam name (elabModuleExp m)
    D.Struct structs ->
      CoreFE.FEnv $ elabStructures structs
    D.MApp m1 m2 ->
      CoreFE.App (elabModuleExp m1) (elabModuleExp m2)
    D.MAppt m1 a ->
      CoreFE.TApp (elabModuleExp m1) (elabTyp a)
    D.MAnno m mty ->
      CoreFE.Anno (elabModuleExp m) (elabModTyp mty)

-- (already reversed by desugaring)
elabStructures :: D.Structures -> CoreFE.Env
elabStructures = map elabStructure

elabStructure :: D.Structure -> CoreFE.EnvE
elabStructure struct =
  case struct of
    D.Let name maybeTyp e ->
      case maybeTyp of
        Nothing -> CoreFE.ModE name (elabExp e)
        Just ty -> CoreFE.ModE name (CoreFE.Anno (elabExp e) (elabTyp ty))
    D.TypDecl name ty ->
      CoreFE.TypE name (elabTyp ty)
    D.ModTypDecl name mty ->
      CoreFE.TypE name (elabModTyp mty)
    D.ModStruct name maybeTyp mod1 ->
      case maybeTyp of
        Nothing -> CoreFE.ModE name (elabModuleExp mod1)
        Just mty -> CoreFE.ModE name (CoreFE.Anno (elabModuleExp mod1) (elabModTyp mty))

elabExp :: D.Exp -> CoreFE.Exp
elabExp e =
  case e of
    D.Lit i -> CoreFE.Lit i
    D.Var n -> CoreFE.Var n
    D.Fix n e1 -> CoreFE.Fix n (elabExp e1)
    D.If e1 e2 e3 -> CoreFE.If (elabExp e1) (elabExp e2) (elabExp e3)
    D.Lam name _ e1 -> CoreFE.Lam name (elabExp e1)
    D.TLam name e1 -> CoreFE.TLam name (elabExp e1)
    D.Clos env e1 ->
      CoreFE.Clos (elabEnv env) (elabExp e1)
    D.App e1 e2 -> CoreFE.App (elabExp e1) (elabExp e2)
    D.TClos env e1 ->
      CoreFE.TClos (elabEnv env) (elabExp e1)
    D.TApp e1 t ->
      CoreFE.TApp (elabExp e1) (elabTyp t)
    D.Box env e1 ->
      CoreFE.Box (elabEnv env) (elabExp e1)
    D.Rec records ->
      CoreFE.FEnv $ map (CoreFE.ExpE "_") $ elabRecords records
    D.RProj e1 n ->
      CoreFE.RProj (elabExp e1) n
    D.FEnv env ->
      CoreFE.FEnv (elabEnv env)
    D.Anno e1 ty ->
      CoreFE.Anno (elabExp e1) (elabTyp ty)
    D.Mod m -> elabModuleExp m
    D.DataCon ctor arg _ty ->
      CoreFE.DataCon ctor (elabExp arg)
    D.Case scrutinee branches ->
      CoreFE.Case (elabExp scrutinee) (map elabCaseBranch branches)
    D.Fold ty e1 ->
      CoreFE.Fold (elabTyp ty) (elabExp e1)
    D.Unfold e1 ->
      CoreFE.Unfold (elabExp e1)
    D.BinOp (D.Add e1 e2) ->
      CoreFE.BinOp (CoreFE.Add (elabExp e1) (elabExp e2))
    D.BinOp (D.Sub e1 e2) ->
      CoreFE.BinOp (CoreFE.Sub (elabExp e1) (elabExp e2))
    D.BinOp (D.Mul e1 e2) ->
      CoreFE.BinOp (CoreFE.Mul (elabExp e1) (elabExp e2))
    D.BinOp (D.EqEq e1 e2) ->
      CoreFE.BinOp (CoreFE.EqEq (elabExp e1) (elabExp e2))
    D.BinOp (D.Neq e1 e2) ->
      CoreFE.BinOp (CoreFE.Neq (elabExp e1) (elabExp e2))
    D.BinOp (D.Lt e1 e2) ->
      CoreFE.BinOp (CoreFE.Lt (elabExp e1) (elabExp e2))
    D.BinOp (D.Le e1 e2) ->
      CoreFE.BinOp (CoreFE.Le (elabExp e1) (elabExp e2))
    D.BinOp (D.Gt e1 e2) ->
      CoreFE.BinOp (CoreFE.Gt (elabExp e1) (elabExp e2))
    D.BinOp (D.Ge e1 e2) ->
      CoreFE.BinOp (CoreFE.Ge (elabExp e1) (elabExp e2))
    D.EList es -> CoreFE.EList (map elabExp es)
    D.ETake i e1 -> CoreFE.ETake i (elabExp e1)

elabRecords :: [(EnvML.Name, D.Exp)] -> [CoreFE.Exp]
elabRecords [] = []
elabRecords ((n, e) : rest) =
  CoreFE.Rec n (elabExp e) : elabRecords rest

-- Environments are already reversed by desugaring
elabEnv :: D.Env -> CoreFE.Env
elabEnv = map elabEnvE

elabEnvE :: D.EnvE -> CoreFE.EnvE
elabEnvE envE =
  case envE of
    D.ExpEN name e -> CoreFE.ExpE name (elabExp e)
    D.ExpE e -> CoreFE.ExpE "_" (elabExp e)
    D.TypEN name ty -> CoreFE.TypE name (elabTyp ty)
    D.TypE ty -> CoreFE.TypE "_" (elabTyp ty)
    D.ModE name m -> CoreFE.ModE name (elabModule m)
    D.ModTypE name mty -> CoreFE.TypE name (elabModTyp mty)

elabTyp :: EnvML.Typ -> CoreFE.Typ
elabTyp ty = case ty of
    EnvML.TyLit lit -> CoreFE.TyLit lit
    EnvML.TyVar n -> CoreFE.TyVar n
    EnvML.TyArr ta tb -> CoreFE.TyArr (elabTyp ta) (elabTyp tb)
    EnvML.TyAll n ty1 -> CoreFE.TyAll n (elabTyp ty1)
    EnvML.TyBoxT ctx ty1 -> CoreFE.TyBoxT (elabTyCtx ctx) (elabTyp ty1)
    EnvML.TyRcd fields -> CoreFE.TyEnvt $ map (CoreFE.Type "_") $ elabRcdFieldsTy fields
    EnvML.TySum ctors ->
      CoreFE.TySum [(name, elabTyp payloadTy) | (name, payloadTy) <- ctors]
    EnvML.TyMu n ty1 ->
      CoreFE.TyMu n (elabTyp ty1)
    EnvML.TyCtx ctx -> CoreFE.TyEnvt (elabTyCtx ctx)
    EnvML.TyModule mty -> elabModTyp mty
    EnvML.TyList ty1 -> CoreFE.TyList (elabTyp ty1)

-- TyCtx is already reversed by desugaring
elabTyCtx :: EnvML.TyCtx -> CoreFE.TyEnv
elabTyCtx = map elabTyCtxE

elabTyCtxE :: EnvML.TyCtxE -> CoreFE.TyEnvE
elabTyCtxE ctxE =
  case ctxE of
    EnvML.TypeN name ty ->
      CoreFE.Type name (elabTyp ty)
    EnvML.Type ty ->
      CoreFE.Type "_" (elabTyp ty)
    EnvML.KindN name -> CoreFE.Kind name
    EnvML.Kind -> CoreFE.Kind "_"
    EnvML.TypeEqN name ty ->
      CoreFE.TypeEq name (elabTyp ty)
    EnvML.TyMod name mty ->
      CoreFE.Type name (elabModTyp mty)
    EnvML.TypeEqM name mty ->
      CoreFE.TypeEq name (elabModTyp mty)

elabRcdFieldsTy :: [(EnvML.Name, EnvML.Typ)] -> [CoreFE.Typ]
elabRcdFieldsTy [] = []
elabRcdFieldsTy ((n, ty) : rest) =
  CoreFE.TyRcd n (elabTyp ty) : elabRcdFieldsTy rest

elabCaseBranch :: D.CaseBranch -> CoreFE.CaseBranch
elabCaseBranch (D.CaseBranch ctor binder body) =
  CoreFE.CaseBranch ctor binder (elabExp body)

elabModTyp :: EnvML.ModuleTyp -> CoreFE.Typ
elabModTyp mty =
  case mty of
    EnvML.TyArrowM ty rest ->
      CoreFE.TyArr (elabTyp ty) (elabModTyp rest)
    EnvML.ForallM name rest ->
      CoreFE.TyAll name (elabModTyp rest)
    EnvML.TySig intf ->
      CoreFE.TyEnvt (elabIntf intf)
    EnvML.TyVarM name ->
      CoreFE.TyVar name

elabIntf :: EnvML.Intf -> CoreFE.TyEnv
elabIntf = map elabIntfE . reverse

elabIntfE :: EnvML.IntfE -> CoreFE.TyEnvE
elabIntfE ie =
  case ie of
    EnvML.TyDef name ty ->
      CoreFE.TypeEq name (elabTyp ty)
    EnvML.ValDecl name ty ->
      CoreFE.Type name (CoreFE.TyRcd name (elabTyp ty))
    EnvML.ModDecl name ty ->
      CoreFE.Type name (elabTyp ty)
    EnvML.FunctorDecl name _args ty ->
      CoreFE.Type name (elabTyp ty)
    EnvML.SigDecl name intf ->
      CoreFE.TypeEq name (CoreFE.TyEnvt (elabIntf intf))