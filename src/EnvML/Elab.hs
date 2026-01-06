module EnvML.Elab where

import qualified EnvML.Syntax      as EnvML
import qualified CoreForAll.Syntax as Core

elabTyEnv ::
  EnvML.TyEnv
  -> Core.TyEnv
elabTyEnv = map elabTyEnvE

elabTyEnvE ::
  EnvML.TyEnvE
  -> Core.TyEnvE
elabTyEnvE (EnvML.Type t)   = Core.Type   $ elabTyp [] t
elabTyEnvE EnvML.Kind       = Core.Kind
elabTyEnvE (EnvML.TypeEq t) = Core.TypeEq $ elabTyp [] t

elabModTyp ::
  EnvML.TyEnv
  -> EnvML.ModuleTyp
  -> Core.Typ
elabModTyp _ (EnvML.TySig intf)     = Core.TyEnvt $ elabIntf [] intf  
elabModTyp _ (EnvML.TyArrowM a sigB)= Core.TyArr (elabTyp [] a) (elabModTyp [] sigB)

elabIntf ::
  EnvML.TyEnv
  -> EnvML.Intf
  -> Core.TyEnv
elabIntf g = map (elabIntfE g)

elabIntfE ::
  EnvML.TyEnv
  -> EnvML.IntfE
  -> Core.TyEnvE
elabIntfE g (EnvML.TyDef t)     = Core.Type $ elabTyp g t
elabIntfE g (EnvML.ValDecl ty)  = Core.Type $ elabTyp g ty
elabIntfE g (EnvML.ModDecl intf)= Core.Type $ Core.TyEnvt $ elabIntf g intf
elabIntfE g (EnvML.SigDecl mty) = Core.Type $ elabModTyp g mty

elabTyp ::
  EnvML.TyEnv
  -> EnvML.Typ
  -> Core.Typ
elabTyp env = error "Types elaboration to do"

elabTyLit ::
  EnvML.TyEnv
  -> EnvML.TyLit
  -> Core.TyLit
elabTyLit = error "Literal types elaboration to do"

elabEnv ::
  EnvML.TyEnv
  -> EnvML.Env
  -> (EnvML.TyEnv, Core.Env)
elabEnv = error "Environments elaboration to do"

elabEnvE ::
  EnvML.TyEnv
  -> EnvML.EnvE
  -> (EnvML.TyEnvE, Core.EnvE)
elabEnvE = error "Environments elaboration to do"

elabInferM :: 
  EnvML.TyEnv 
  -> EnvML.Module
  -> (EnvML.Typ, Core.Exp)
elabInferM = error "Module elaboration to do"

elabExp ::
  EnvML.TyEnv
  -> EnvML.Exp
  -> Core.Exp
elabExp = error "Expression elaboration to do"

elabLit ::
  EnvML.TyEnv
  -> EnvML.Literal
  -> Core.Literal
elabLit = error "Expression elaboration to do"


