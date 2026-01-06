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
  deriving (Eq)

data ModuleTyp
  = TySig    Intf
  | TyArrowM Typ ModuleTyp
  deriving (Eq)

type Intf = [IntfE]         -- (sig ... end) .eli

data IntfE 
  = TyDef    Typ       -- (type t = ...)   
  | ValDecl  Typ       -- (val x : t)
  | ModDecl  Intf      -- (module M : S)
  | SigDecl  ModuleTyp -- (module type S = ...)
  deriving (Eq)

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
  deriving (Eq)

data TyLit 
  = TyInt                   -- int
  | TyBool                  -- bool
  | TyStr                   -- string
  deriving (Eq)

-- Environment
type Env = [EnvE]

-- Environment elements
data EnvE 
  = ExpE Exp 
  | TypE Typ
  deriving (Eq)

data Module
  = Functor Typ Module      -- functor (x : A) struct x end
  | Struct  Env             -- struct type a = int; x = 1 end
  | MApp    Module Module   -- M1 M2
  | MLink   Module Module   -- M1 |><| M2    
  deriving (Eq)

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
  deriving (Eq)

data Literal 
  = LitInt  Int             -- 1, 2, etc.
  | LitBool Bool            -- false, true
  | LitStr  String          -- "hello"
  deriving (Eq)

