module Core.Syntax where

type TyEnv = [TyEnvE]

data TyEnvE
  = Type Typ
  | Kind
  | TypeEq Typ
  deriving (Eq, Show)

data Typ
  = TyLit TyLit
  | TyVar Int
  | TyArr Typ Typ
  | TyAll Typ
  | TyBoxT TyEnv Typ
  | TySubstT Typ Typ
  | TyRcd String Typ
  | TyEnvt TyEnv
  deriving (Eq, Show)

data TyLit
  = TyInt -- int
  | TyBool -- bool
  | TyStr -- string
  deriving (Eq, Show)

-- Environment
type Env = [EnvE]

-- Environment elements
data EnvE = ExpE Exp | TypE Typ
  deriving (Eq, Show)

data Exp
  = Lit Literal
  | -- De-bruijn index
    Var Int
  | -- Term abstractions etc.
    Lam Exp
  | Clos Env Exp
  | App Exp Exp
  | -- Type abstractions etc.
    TLam Exp
  | TClos Env Exp
  | TApp Exp Typ
  | -- Box
    Box Env Exp
  | -- Records
    Rec String Exp
  | RProj Exp String
  | -- First-class Environment
    FEnv Env
  | Anno Exp Typ
  | -- Extensions
    Fix Exp
  | If Exp Exp Exp
  | BinOp BinOp
  deriving (Eq, Show)

data BinOp
  = Add Exp Exp
  | Sub Exp Exp
  | Mul Exp Exp
  | EqEq Exp Exp
  deriving (Eq, Show)

data Literal
  = LitInt Int -- 1, 2, etc.
  | LitBool Bool -- false, true
  | LitStr String -- "hello"
  deriving (Eq, Show)
