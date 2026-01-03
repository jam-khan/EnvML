{-# LANGUAGE InstanceSigs #-}
module EnvML.Syntax where


main :: IO ()
main = print "EnvML Syntax"

type Name = String

type TyEnv = [(Name, TyEnvE)] -- [t : A, t1 : Type, t2 : A=]

data TyEnvE
  = Type    Typ             -- A
  | Kind                    -- Type
  | TypeEq  Typ             -- A=
  deriving (Eq)

data ModuleTyp
  = TyArrowM Typ ModuleTyp  -- (A ->m I)
  | TySig    Intf           -- (sig .. end)
  deriving (Eq)

type Intf = [IntfE]         -- (sig ... end) .eli

data IntfE 
  = TyDef    Name Typ       -- (type t = ...)   
  | ValDecl  Name Typ       -- (val x : t)
  | ModDecl  Name Name      -- (module M : S)
  | SigDecl  Name ModuleTyp -- (module type S = ...)
  deriving (Eq)

data Typ
  = TyLit    TyLit          -- int, bool, or string
  | TyVar    Name           -- a
  | TyArr    Typ Typ        -- A -> B
  | TyAll    Name Typ       -- forall a'. T
  | TyBoxT   TyEnv Typ      -- [t1 : int, t2 : int, t3: bool] ==> A
  | TySubstT Typ Name Typ   -- A[x:=B]
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
type Env = [(Name, EnvE)]

-- Environment elements
data EnvE 
  = ExpE Exp 
  | TypE Typ
  deriving (Eq)

data Module
  = Functor Name Typ Module -- functor (x : A) struct x end
  | Struct  Env             -- struct type a = int; x = 1 end
  | MApp    Module Module   -- M1 M2
  | MLink   Module Module   -- M1 |><| M2    
  deriving (Eq)

data Exp
  = Lit   Literal           -- Literals: int, double, bool, string
  | Var   Name              -- Var x, y, hello
  | Lam   Name Typ Exp      -- fun (x: A) -> x + 1
  | Clos  Env Name Typ Exp  -- clos [t = int, x = 1] (y: t) -> x + y
  | App   Exp Exp           -- f(x)
  | TLam  Name Exp          -- fun type a' -> fun (x: a') -> x
  | TClos Env Name Exp      -- clos [type t = int, x = 1] -> 
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

instance Show Literal where
  show :: Literal -> String
  show (LitInt i)  = show i
  show (LitBool b) = if b then "true" else "false"
  show (LitStr s)  = show s

showEnv :: TyEnv -> String
showEnv env = "[" ++ showEnv' env ++ "]"
  where 
    showEnv' :: TyEnv -> String
    showEnv' [] = ""
    showEnv' ((x, t):xs) = x ++ ": " ++ show t ++ ", " ++ show xs

instance Show TyEnvE where
  show :: TyEnvE -> String
  show (Type t)   = show t
  show Kind       = "Type"
  show (TypeEq t) = "(" ++ show t ++ ")="

instance Show ModuleTyp where
  show :: ModuleTyp -> String
  show (TyArrowM typ typm) = "(" ++ show typ ++ " ->m " ++ show typm ++ ")"
  show (TySig intf)        = "sig " ++ showIntf intf ++ " end"
    where 
      showIntf :: Intf -> String
      showIntf []     = "[]"
      showIntf (x:xs) = show x ++ "; " ++ show xs

instance Show IntfE where
  show :: IntfE -> String
  show (TyDef x ty)   = "type " ++ x ++ " = " ++ show ty
  show (ValDecl x ty) = "val "  ++ x ++ " : " ++ show ty
  show (ModDecl x s)  = "module " ++ x ++ " : " ++ s
  show (SigDecl x ty) = "module type " ++ x ++ " = " ++ show ty

instance Show Typ where
  show :: Typ -> String
  show (TyLit lit)       = show lit
  show (TyVar x)         = x
  show (TyArr tyA tyB)   = show tyA ++ "(" ++ show tyB ++ ")"
  show (TyAll x ty)      = "forall " ++ x ++ ". (" ++ show ty ++ ")"
  show (TyBoxT tye ty)   = show tye ++ "=>" ++ show ty
  show (TySubstT t1 x t2)= "("++ show t1 ++ ")" ++ "[" ++ x ++ ":=" ++ show t2 ++ "]"
  show (TyRcd x a)       = "{" ++ x ++ ":" ++ show a ++ "}"
  show (TyEnvt env)      = showEnv env
  show (TyModule typm)   = "sig:" ++ "(" ++ show typm ++ ")"

instance Show TyLit where
  show :: TyLit -> String
  show TyInt  = "int"
  show TyBool = "bool"
  show TyStr  = "string"

