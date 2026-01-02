module EnvML.Elab where

import qualified EnvML.Syntax      as EnvML
import qualified CoreForAll.Syntax as Core

elabTyEnv ::
  EnvML.TyEnv
  -> Core.TyEnvE
elabTyEnv = error "Type Environment Elaboration To Do"

elabModTyp ::
  EnvML.TyEnv
  -> EnvML.ModuleTyp
  -> Core.Typ
elabModTyp = error "Module type elaboration to do"

elabIntf ::
  EnvML.TyEnv
  -> EnvML.Intf
  -> Core.TyEnv
elabIntf = error "Interface elaboration to do"

elabIntfE ::
  EnvML.TyEnv
  -> EnvML.IntfE
  -> Core.TyEnv
elabIntfE = error "Interface elements elaboration to do"

elabTyp ::
  EnvML.TyEnv
  -> EnvML.Typ
  -> Core.Typ
elabTyp = error "Types elaboration to do"

elabTyLit ::
  EnvML.TyEnv
  -> EnvML.TyLit
  -> Core.TyLit
elabTyLit = error "Literal types elaboration to do"

elabEnv ::
  EnvML.TyEnv
  -> EnvML.Env
  -> Core.Env
elabEnv = error "Environments elaboration to do"

elabEnvE ::
  EnvML.TyEnv
  -> EnvML.EnvE
  -> Core.EnvE
elabEnvE = error "Environments elaboration to do"

elabM :: 
  EnvML.TyEnv 
  -> EnvML.Module
  -> Core.Exp
elabM = error "Module elaboration to do"

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


