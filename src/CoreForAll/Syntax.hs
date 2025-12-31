module CoreForAll.Syntax where

data Typ
  = TyInt
  | TyVar    Int
  | TyArr    Typ Typ
  | TyAll    Typ
  | TyBoxT   TyEnv Typ
  | TySubstT Typ Typ
  | TyRcd    String Typ
  | TyEnvt   TyEnv
  deriving (Eq, Show)

type TyEnv = [TyEnvE]

data TyEnvE
  = Type    Typ
  | Kind 
  | TypeEq  Typ
  deriving (Eq, Show)

data Exp
  = Lit   Int
  -- De-bruijn index
  | Var   Int
  -- Term abstractions etc.
  | Lam   Exp
  | Clos  Env Exp
  | App   Exp Exp
  -- Type abstractions etc.
  | TLam  Exp
  | TClos Env Exp
  | TApp  Exp Typ
  -- Box
  | Box   Env Exp
  -- Records
  | Rec   String Exp
  | RProj Exp String
  -- First-class Environment
  | FEnv  Env
  | Anno  Exp Typ
  deriving (Eq, Show)

-- Environment
type Env = [EnvE]

-- Environment elements
data EnvE = ExpE Exp | TypE Typ
  deriving (Eq, Show)

