module Core.Named where
import qualified Core.Syntax as Nameless

type Name = String

type Env = [EnvE]
-- Distinction between x = e and m = e is to differentiate between record projection variable vs. expression variable
data EnvE 
  = ExpE Name Exp -- x = e
  | ModE Name Exp -- m = ..
  | TypE Name Typ -- t = A
  deriving (Eq, Show)

data Exp
  = Lit   Nameless.Literal
  | Var   Name
  | Lam   Name Exp
  | Clos  Env Exp
  | App   Exp Exp
  | TLam  Name Exp
  | TClos Env Exp
  | TApp  Exp Typ
  | Box   Env Exp
  | Rec   String Exp
  | RProj Exp String
  | FEnv  Env
  | Anno  Exp Typ
  deriving (Eq, Show)

type TyEnv = [TyEnvE]
data TyEnvE
  = Type   Name Typ -- A
  | Kind   Name     -- *
  | TypeEq Name Typ -- eq A
  deriving (Eq, Show)

data Typ
  = TyLit    Nameless.TyLit -- int, bool, string
  | TyVar    Name           -- t
  | TyArr    Typ Typ        -- A -> A
  | TyAll    Name Typ       -- ∀t. A
  | TyBoxT   TyEnv Typ      -- Γ ▷ A
  | TySubstT Name Typ Typ   -- [t = A] B
  | TyRcd    String Typ     -- {l : A}
  | TyEnvt   TyEnv          -- Γ
  deriving (Eq, Show)
