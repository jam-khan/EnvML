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
  = TyArrowM Typ ModuleTyp -- A ->m I
  | ForallM  ModuleTyp     -- ∀. I
  | TySig    Intf          -- I
  | TyVarM   Int           -- M (* type variable in signature *)
  deriving (Show, Eq)

type Intf   = [IntfE]  -- (sig ... end) .eli

data IntfE
  = TyDef    Typ       -- (type t = ...)   
  | ValDecl  Typ       -- (val x : t)
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
  | TyRcd    [(Name, Typ)]  -- {l : A}
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
  = VarM     Int             -- module variable
  | Functor  Module          -- functor (x : A) struct x end    ~~> lambda
  | Functort Module          -- functor (t : type) struct x end ~~> Big Lambda
  | Struct   Env             -- struct type a = int; x = 1 end  ~~> Env
  | MApp     Module Module   -- M1 ^ M2                         ~~> e1 e2
  | MAppt    Module Typ      -- M1 ^@ A                         ~~> e1 @A
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
  | Rec   [(Name,Exp)]      -- {l1 = A1, ..., l2=A2}
  | RProj Exp Name          -- e.l
  | FEnv  Env               -- [type a = int, x = 1]
  | Anno  Exp Typ           -- (e::A)
  | ModE  Module            -- functor or struct
-- Extensions
  | BinOp BinOp
  deriving (Show, Eq)

data BinOp
  = Add Exp Exp
  | Sub Exp Exp
  | Mul Exp Exp
  deriving (Show, Eq)

data Literal 
  = LitInt  Int             -- 1, 2, etc.
  | LitBool Bool            -- false, true
  | LitStr  String          -- "hello"
  deriving (Show, Eq)

class Pretty a where
  pretty :: a -> String

instance Pretty Typ where
  pretty :: Typ -> String
  pretty = prettyTyp

instance Pretty Exp where
  pretty :: Exp -> String
  pretty = prettyExp

instance Pretty Module where
  pretty :: Module -> String
  pretty = prettyModule

instance Pretty Literal where
  pretty :: Literal -> String
  pretty = prettyLiteral

instance Pretty TyLit where
  pretty :: TyLit -> String
  pretty = prettyTyLit

instance Pretty TyEnvE where
  pretty :: TyEnvE -> String
  pretty = prettyTyEnvE

instance Pretty IntfE where
  pretty :: IntfE -> String
  pretty = prettyIntfE

instance Pretty ModuleTyp where
  pretty :: ModuleTyp -> String
  pretty = prettyModuleTyp

parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s

-- Precedence

type Precedence = Int

typPrec :: Typ -> Precedence
typPrec t = case t of
  TyLit _     -> 4
  TyVar _     -> 4
  TyRcd {}    -> 4
  TyEnvt _    -> 4
  TyModule _  -> 4
  TySubstT {} -> 3
  TyArr _ _   -> 2
  TyBoxT _ _  -> 1
  TyAll _     -> 1

expPrec :: Exp -> Precedence
expPrec e = case e of
  Anno _ _  -> 0
  Box _ _   -> 1
  Clos {}   -> 1
  TClos {}  -> 1
  Lam {}    -> 2
  TLam {}   -> 2
  App _ _   -> 3
  TApp _ _  -> 3
  RProj _ _ -> 3
  Lit _     -> 5
  Var _     -> 5
  Rec {}    -> 5
  FEnv _    -> 5
  ModE _    -> 5
  _         -> 4 -- BinOp and others

-- TyEnv pretty printing
prettyTyEnvE :: TyEnvE -> String
prettyTyEnvE (Type t) = prettyTyp t
prettyTyEnvE Kind = "Type"
prettyTyEnvE (TypeEq t) = "type = " ++ prettyTyp t

prettyTyEnv :: TyEnv -> String
prettyTyEnv [] = ""
prettyTyEnv [e] = prettyTyEnvE e
prettyTyEnv (e : es) = prettyTyEnvE e ++ ", " ++ prettyTyEnv es

-- Env pretty printing
prettyEnvE :: EnvE -> String
prettyEnvE (ExpE e) = prettyExp e
prettyEnvE (TypE t) = prettyTyp t
prettyEnvE (ModExpE e) = "module " ++ prettyExp e
prettyEnvE (ModTypE t) = "module type " ++ prettyTyp t

prettyEnv :: Env -> String
prettyEnv [] = ""
prettyEnv [e] = prettyEnvE e
prettyEnv (e : es) = prettyEnvE e ++ ", " ++ prettyEnv es

-- Interface pretty printing
prettyIntfE :: IntfE -> String
prettyIntfE (TyDef t) = "type = " ++ prettyTyp t
prettyIntfE (ValDecl t) = "val : " ++ prettyTyp t
prettyIntfE (ModDecl t) = "module : " ++ prettyTyp t
prettyIntfE (SigDecl t) = "module type = " ++ prettyTyp t

prettyIntf :: Intf -> String
prettyIntf [] = ""
prettyIntf [e] = prettyIntfE e
prettyIntf (e : es) = prettyIntfE e ++ "; " ++ prettyIntf es

-- ModuleTyp pretty printing
prettyModuleTyp :: ModuleTyp -> String
prettyModuleTyp (TyArrowM t m) = 
  prettyTyp t ++ " ->m " ++ prettyModuleTyp m
prettyModuleTyp (ForallM m) = 
  "∀. " ++ prettyModuleTyp m
prettyModuleTyp (TySig intf) = 
  "sig " ++ prettyIntf intf ++ " end"
prettyModuleTyp (TyVarM i) = "M" ++ show i

-- Type pretty printing
prettyTyp :: Typ -> String
prettyTyp (TyLit l) = prettyTyLit l
prettyTyp (TyVar i) = "t" ++ show i
prettyTyp (TyArr t1 t2) =
  let s1 = parensIf (typPrec t1 < typPrec (TyArr t1 t2)) (prettyTyp t1)
      s2 = prettyTyp t2
   in s1 ++ " -> " ++ s2
prettyTyp (TyAll t) =
  let s = parensIf (typPrec t < typPrec (TyAll t)) (prettyTyp t)
   in "forall. " ++ s
prettyTyp (TyBoxT ctx t) =
  let sCtx = prettyTyEnv ctx
      sTyp = parensIf (typPrec t < typPrec (TyBoxT ctx t)) (prettyTyp t)
   in "[" ++ sCtx ++ "] ==> " ++ sTyp
prettyTyp (TySubstT t1 t2) =
  let s1 = parensIf (typPrec t1 < typPrec (TySubstT t1 t2)) (prettyTyp t1)
      s2 = prettyTyp t2
   in s1 ++ "[" ++ s2 ++ "]"
prettyTyp (TyEnvt ctx) = "[" ++ prettyTyEnv ctx ++ "]"
prettyTyp (TyRcd []) = "{}"
prettyTyp (TyRcd fields) = 
  "{" ++ intercalateComma (map (\(l, t) -> l ++ " : " ++ prettyTyp t) fields) ++ "}"
  where
    intercalateComma [] = ""
    intercalateComma [x] = x
    intercalateComma (x:xs) = x ++ ", " ++ intercalateComma xs
prettyTyp (TyModule mt) = prettyModuleTyp mt

prettyTyLit :: TyLit -> String
prettyTyLit TyInt = "int"
prettyTyLit TyBool = "bool"
prettyTyLit TyStr = "string"

-- Module pretty printing
prettyModule :: Module -> String
prettyModule (VarM i) = "M" ++ show i
prettyModule (Functor m) =
  "functor -> " ++ prettyModule m
prettyModule (Functort m) =
  "functor (type) -> " ++ prettyModule m
prettyModule (Struct env) =
  "struct " ++ prettyEnv env ++ " end"
prettyModule (MApp m1 m2) = 
  prettyModule m1 ++ " ^ " ++ prettyModule m2
prettyModule (MAppt m t) = 
  prettyModule m ++ " ^@ " ++ prettyTyp t

-- Expression pretty printing
prettyExp :: Exp -> String
prettyExp (Lit l) = prettyLiteral l
prettyExp (Var i) = "v" ++ show i
prettyExp (Lam e) = 
  "fun -> " ++ 
  parensIf (expPrec e < expPrec (Lam e)) (prettyExp e)
prettyExp (TLam e) = 
  "fun type -> " ++ 
  parensIf (expPrec e < expPrec (TLam e)) (prettyExp e)
prettyExp (Clos env e) = 
  "clos [" ++ prettyEnv env ++ "] -> " ++ 
  parensIf (expPrec e < expPrec (Clos env e)) (prettyExp e)
prettyExp (TClos env e) = 
  "tclos [" ++ prettyEnv env ++ "] -> " ++ 
  parensIf (expPrec e < expPrec (TClos env e)) (prettyExp e)
prettyExp (App e1 e2) = 
  parensIf (expPrec e1 < expPrec (App e1 e2)) (prettyExp e1) ++ 
  "(" ++ prettyExp e2 ++ ")"
prettyExp (TApp e t) = 
  parensIf (expPrec e < expPrec (TApp e t)) (prettyExp e) ++ 
  "<" ++ prettyTyp t ++ ">"
prettyExp (Box env e) = 
  "box [" ++ prettyEnv env ++ "] in " ++ 
  parensIf (expPrec e < expPrec (Box env e)) (prettyExp e)
prettyExp (Rec []) = "{}"
prettyExp (Rec fields) = 
  "{" ++ intercalateComma (map (\(l, e) -> l ++ " = " ++ prettyExp e) fields) ++ "}"
  where
    intercalateComma [] = ""
    intercalateComma [x] = x
    intercalateComma (x:xs) = x ++ ", " ++ intercalateComma xs
prettyExp (RProj e label) = 
  parensIf (expPrec e < expPrec (RProj e label)) (prettyExp e) ++ "." ++ label
prettyExp (FEnv env) = "[" ++ prettyEnv env ++ "]"
prettyExp (Anno e t) = 
  parensIf (expPrec e < expPrec (Anno e t)) (prettyExp e) ++ " :: " ++ prettyTyp t
prettyExp (ModE m) = prettyModule m
prettyExp (BinOp op) = prettyBinOp op

prettyBinOp :: BinOp -> String
prettyBinOp (Add e1 e2) = prettyExp e1 ++ " + " ++ prettyExp e2
prettyBinOp (Sub e1 e2) = prettyExp e1 ++ " - " ++ prettyExp e2
prettyBinOp (Mul e1 e2) = prettyExp e1 ++ " * " ++ prettyExp e2

prettyLiteral :: Literal -> String
prettyLiteral (LitInt i) = show i
prettyLiteral (LitBool b) = if b then "true" else "false"
prettyLiteral (LitStr s) = show s