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
  = TyInt
  | TyBool
  | TyStr
  deriving (Eq, Show)

type Env = [EnvE]

data EnvE = ExpE Exp | TypE Typ
  deriving (Eq, Show)

data Exp
  = Lit   Literal
  | Var   Int
  | Lam   Exp
  | Clos  Env Exp
  | App   Exp Exp
  | TLam  Exp
  | TClos Env Exp
  | TApp  Exp Typ
  | Box   Env Exp
  | Rec   String Exp
  | RProj Exp String
  | FEnv  Env
  | Anno  Exp Typ
  | Fix   Exp
  | If    Exp Exp Exp
  | BinOp BinOp
  deriving (Eq, Show)

data BinOp
  = Add   Exp Exp
  | Sub   Exp Exp
  | Mul   Exp Exp
  | EqEq  Exp Exp
  deriving (Eq, Show)

data Literal
  = LitInt  Int
  | LitBool Bool
  | LitStr  String
  deriving (Eq, Show)
