{-# LANGUAGE InstanceSigs #-}
module EnvML.Syntax where


main :: IO ()
main = print "EnvML Syntax"

type Name = String

type TyEnv = [TyEnvE]

data TyEnvE
  = Type    Typ
  | Kind
  | TypeEq  Typ
  deriving (Show, Eq)

data ModuleTyp
  = TySig    Intf
  | TyArrowM Typ ModuleTyp
  deriving (Show, Eq)

type Intf = [IntfE]         -- (sig ... end) .eli

data IntfE 
  = TyDef    Typ       -- (type t = ...)   
  | ValDecl  Typ       -- (val x : t)
-- Note: ModDecl and SigDecl accept Typ because they can refer to variables
  | ModDecl  Typ       -- (module M : S)
  | SigDecl  Typ       -- (module type S = ...)
  deriving (Show, Eq)

data Typ
  = TyLit    TyLit          -- int, bool, or string
  | TyVar    Int            -- a
  | TyArr    Typ Typ        -- A -> B
  | TyAll    Typ            -- forall a'. T
  | TyBoxT   TyEnv Typ      -- [t1 : int, t2 : int, t3: bool] ==> A
  | TySubstT Typ Typ        -- A[x:=B]
  | TyRcd    String Typ     -- {l : A}
  | TyEnvt   TyEnv          -- [t : A, t1 : Type, t2 : A=]
  | TyModule ModuleTyp      -- Note: First-class modules   
  deriving (Show, Eq)

data TyLit 
  = TyInt                   -- int
  | TyBool                  -- bool
  | TyStr                   -- string
  deriving (Show, Eq)

-- Environment
type Env = [EnvE]

-- Environment elements
data EnvE 
  = ExpE Exp 
  | TypE Typ
-- Note: ModExpE and TypExpE accept Exp and Typ respectively because they can refer to variables
  | ModExpE Exp
  | ModTypE Typ
  deriving (Show, Eq)

data Module
  = Functor Typ Module      -- functor (x : A) struct x end
  | Struct  Env             -- struct type a = int; x = 1 end
  | MApp    Module Module   -- M1 M2
  | MLink   Module Module   -- M1 |><| M2    
  deriving (Show, Eq)

data Exp
  = Lit   Literal           -- Literals: int, double, bool, string
  | Var   Int               -- Var x, y, hello
  | Lam   Exp               -- fun (x: A) -> x + 1
  | Clos  Env Exp           -- clos [t = int, x = 1] (y: t) -> x + y
  | App   Exp Exp           -- f(x)
  | TLam  Exp               -- fun type a' -> fun (x: a') -> x
  | TClos Env Exp           -- clos [type t = int, x = 1] -> 
  | TApp  Exp Typ           -- f<t>
  | Box   Env Exp           -- box [type t = int, x = 1] in e 
  | Rec   Name Exp          -- {l = A}
  | RProj Exp Name          -- e.l
  | FEnv  Env               -- [type a = int, x = 1]
  | Anno  Exp Typ           -- (e::A)
  | ModE  Module            -- functor or struct
  deriving (Show, Eq)

data Literal 
  = LitInt  Int             -- 1, 2, etc.
  | LitBool Bool            -- false, true
  | LitStr  String          -- "hello"
  deriving (Show, Eq)

