{-# LANGUAGE InstanceSigs #-}

module EnvML.Parser.AST where

main :: IO ()
main = print "EnvML Parsed AST"

-- AST with names and direct source-level representation

type Name     = String            -- Alias for naming
type Imports  = [(Name, Typ)]     -- import x : A

type FunArgs = [(Name, FunArg)]
data FunArg
  = TyArg
  | TmArg
  | TmArgType Typ
  deriving (Show, Eq)

type TyCtx    = [TyCtxE]  -- [t : A, t1 : Type, type t2 = A]
data TyCtxE
  = TypeN    Name Typ       -- t : A
  | Type     Typ            -- nameless A
  | KindN    Name           -- t : *
  | Kind                    -- nameless *
  | TypeEqN  Name Typ       -- type x = A !Must be named
  | TyMod    Name ModuleTyp -- module n : A
  | TypeEqM  Name ModuleTyp -- module type m = .. 
  deriving (Show, Eq)

data ModuleTyp
  = TyArrowM  Typ ModuleTyp   -- (A ->m I)
  | ForallM   Name ModuleTyp  -- ∀t. I
  | TySig     Intf            -- (sig .. end)
  deriving (Show, Eq)

type Intf = [IntfE]           -- (sig ... end) .eli
data IntfE
  = TyDef       Name Typ               -- (type t = ...)
  | ValDecl     Name Typ               -- (val x : t)
  | ModDecl     Name ModuleTyp         -- (module M : S)
  | FunctorDecl Name FunArgs ModuleTyp -- (functor m (type t) (x: A) : S)
  | SigDecl     Name Intf              -- (module type S = ...)
  deriving (Show, Eq)

data Typ
  = TyLit     TyLit           -- int, bool, or string
  | TyVar     Name            -- x
  | TyArr     Typ   Typ       -- A -> B
  | TyAll     Name  Typ       -- forall a'. T
  | TyBoxT    TyCtx Typ       -- [t1 : int, t2 : int, t3: bool] ==> A
  | TyRcd     [(Name, Typ)]   -- {l1 : A1, l2 : A2, ln : An}
  | TyCtx     TyCtx           -- [t : A, t1 : Type, t2 : A=]
  | TyModule  ModuleTyp       -- Note: First-class modules
  deriving (Show, Eq)

data TyLit
  = TyInt     -- int
  | TyBool    -- bool
  | TyStr     -- string
  deriving (Show, Eq)

type Env = [EnvE]
data EnvE
  = ExpEN   Name Exp        -- [x = e]
  | ExpE    Exp             -- [e]
  | TypEN   Name Typ        -- [type x = A]
  | TypE    Typ             -- [A]
  | ModE    Name Module     -- [module m = ...]
  | ModTypE Name ModuleTyp  -- [module type A = sig .. end]
  deriving (Show, Eq)

data Module
  = VarM    Name            -- module variable
  | Functor FunArgs Module  -- functor (x : A) ->
  | Struct  Imports Env     -- struct type a = int; x = 1 end
  | MApp    Module Module   -- M1 ^ M2
  | MAppt   Module Typ      -- M1 ^ @A
  | MLink   Module Module   -- link(M1, M2)
  deriving (Show, Eq)

data Exp
  = Lit   Literal         -- Literals: int, double, bool, string
  | Var   Name            -- Var x, y, hello
  | Lam   FunArgs Exp     -- fun (x: A) (y : B) -> x + 1
  | TLam  FunArgs Exp     -- fun 
  | Clos  Env FunArgs Exp -- clos [type t = int, x = 1] (y: t) -> x + y
  | App   Exp Exp         -- f(x)
  | TClos Env FunArgs Exp -- clos [type t = int, x = 1] ->
  | TApp  Exp Typ         -- f<t>
  | Box   Env Exp         -- box [type t = int, x = 1] in e
  | Rec   [(Name, Exp)]   -- {l1 = e1, l2 = e2, l3 = e3}
  | RProj Exp Name        -- e.l
  | FEnv  Env             -- [type a = int, x = 1]
  | Anno  Exp Typ         -- (e::A)
  | Mod   Module          -- functor or struct
  -- Extensions
  | BinOp BinOp
  deriving (Show, Eq)

data BinOp
  = Add Exp Exp
  | Sub Exp Exp
  | Mul Exp Exp
  deriving (Show, Eq)

data Literal
  = LitInt  Int     -- 1, 2, etc.
  | LitBool Bool    -- false, true
  | LitStr  String  -- "hello"
  deriving (Show, Eq)

type Precedence = Int

typPrec :: Typ -> Precedence
typPrec t = case t of
  TyLit _     -> 4
  TyVar _     -> 4
  TyRcd {}    -> 4
  TyCtx _     -> 4
  TyModule _  -> 4
  TyArr _ _   -> 2
  TyBoxT _ _  -> 1
  TyAll _ _   -> 1

expPrec :: Exp -> Precedence
expPrec e = case e of
  Anno _ _  -> 0
  Box _ _   -> 1
  Clos {}   -> 1
  TClos {}  -> 1
  Lam {}    -> 2
  App _ _   -> 3
  TApp _ _  -> 3
  RProj _ _ -> 3
  Lit _     -> 5
  Var _     -> 5
  Rec {}    -> 5
  FEnv _    -> 5
  Mod _     -> 5
  _ -> 4 -- TODO: Extensions



----------------------
-- Pretty Printing ---
----------------------

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

instance Pretty TyCtxE where
  pretty :: TyCtxE -> String
  pretty = prettyTyCtxE

instance Pretty IntfE where
  pretty :: IntfE -> String
  pretty = prettyIntfE

instance Pretty ModuleTyp where
  pretty :: ModuleTyp -> String
  pretty = prettyModuleTyp

parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s

-- TyCtx pretty printing (updated for new TyCtxE constructors)
prettyTyCtxE :: TyCtxE -> String
prettyTyCtxE (TypeN n t) = n ++ " : " ++ prettyTyp t
prettyTyCtxE (Type t) = prettyTyp t
prettyTyCtxE (KindN n) = n ++ " : Type"
prettyTyCtxE Kind = "Type"
prettyTyCtxE (TypeEqN n t) = "type " ++ n ++ " = " ++ prettyTyp t
prettyTyCtxE (TyMod n mt) = "module " ++ n ++ " : " ++ prettyModuleTyp mt
prettyTyCtxE (TypeEqM n mt) = "module type " ++ n ++ " = " ++ prettyModuleTyp mt

prettyTyCtx :: TyCtx -> String
prettyTyCtx [] = ""
prettyTyCtx [e] = prettyTyCtxE e
prettyTyCtx (e : es) = prettyTyCtxE e ++ ", " ++ prettyTyCtx es

-- Env pretty printing (same as before)
prettyEnvE :: EnvE -> String
prettyEnvE (ExpEN n e) = n ++ " = " ++ prettyExp e
prettyEnvE (ExpE e) = prettyExp e
prettyEnvE (TypEN n t) = "type " ++ n ++ " = " ++ prettyTyp t
prettyEnvE (TypE t) = prettyTyp t
prettyEnvE (ModE n m) = "module " ++ n ++ " = " ++ prettyModule m
prettyEnvE (ModTypE n mt) = "module type " ++ n ++ " = " ++ prettyModuleTyp mt

prettyEnv :: Env -> String
prettyEnv [] = ""
prettyEnv [e] = prettyEnvE e
prettyEnv (e : es) = prettyEnvE e ++ ", " ++ prettyEnv es

-- Interface pretty printing (same as before)
prettyIntfE :: IntfE -> String
prettyIntfE (TyDef n t) = "type " ++ n ++ " = " ++ prettyTyp t
prettyIntfE (ValDecl n t) = "val " ++ n ++ " : " ++ prettyTyp t
prettyIntfE (ModDecl n mt) = "module " ++ n ++ " : " ++ prettyModuleTyp mt
prettyIntfE (FunctorDecl n args mt) = 
  "functor " ++ n ++ " " ++ prettyFunArgs args ++ " : " ++ prettyModuleTyp mt
prettyIntfE (SigDecl n intf) = "module type " ++ n ++ " = sig " ++ prettyIntf intf ++ " end"

prettyIntf :: Intf -> String
prettyIntf [] = ""
prettyIntf [e] = prettyIntfE e
prettyIntf (e : es) = prettyIntfE e ++ "; " ++ prettyIntf es

-- FunArgs pretty printing (same as before)
prettyFunArgs :: FunArgs -> String
prettyFunArgs [] = ""
prettyFunArgs [arg] = prettyFunArg arg
prettyFunArgs (arg : args) = prettyFunArg arg ++ " " ++ prettyFunArgs args

prettyFunArg :: (Name, FunArg) -> String
prettyFunArg (n, TyArg) = "(type " ++ n ++ ")"
prettyFunArg (n, TmArg) = "(" ++ n ++ ")"
prettyFunArg (n, TmArgType t) = "(" ++ n ++ " : " ++ prettyTyp t ++ ")"

-- ModuleTyp pretty printing (same as before)
prettyModuleTyp :: ModuleTyp -> String
prettyModuleTyp (TyArrowM t m) = 
  prettyTyp t ++ " ->m " ++ prettyModuleTyp m
prettyModuleTyp (ForallM n m) = 
  "∀" ++ n ++ ". " ++ prettyModuleTyp m
prettyModuleTyp (TySig intf) = 
  "sig " ++ prettyIntf intf ++ " end"

-- Type pretty printing (same as before)
prettyTyp :: Typ -> String
prettyTyp (TyLit l) = prettyTyLit l
prettyTyp (TyVar s) = s
prettyTyp (TyArr t1 t2) =
  let s1 = parensIf (typPrec t1 < typPrec (TyArr t1 t2)) (prettyTyp t1)
      s2 = prettyTyp t2
   in s1 ++ " -> " ++ s2
prettyTyp (TyAll x t) =
  let s = parensIf (typPrec t < typPrec (TyAll x t)) (prettyTyp t)
   in "forall " ++ x ++ ". " ++ s
prettyTyp (TyBoxT ctx t) =
  let sCtx = prettyTyCtx ctx
      sTyp = parensIf (typPrec t < typPrec (TyBoxT ctx t)) (prettyTyp t)
   in "[" ++ sCtx ++ "] ==> " ++ sTyp
prettyTyp (TyCtx ctx) = "[" ++ prettyTyCtx ctx ++ "]"
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

-- Module pretty printing (same as before)
prettyModule :: Module -> String
prettyModule (VarM n) = n
prettyModule (Functor args m) =
  "functor " ++ prettyFunArgs args ++ " -> " ++ prettyModule m
prettyModule (Struct imports env) =
  let sEnv = prettyEnv env
      sImports = concatMap (\(n, t) -> "import " ++ n ++ " : " ++ prettyTyp t ++ "; ") imports
   in "struct " ++ sImports ++ sEnv ++ " end"
prettyModule (MApp m1 m2) = 
  prettyModule m1 ++ " ^ " ++ prettyModule m2
prettyModule (MAppt m t) = 
  prettyModule m ++ " ^@ " ++ prettyTyp t
prettyModule (MLink m1 m2) = 
  "link(" ++ prettyModule m1 ++ ", " ++ prettyModule m2 ++ ")"

-- Expression pretty printing (same as before)
prettyExp :: Exp -> String
prettyExp (Lit l) = prettyLiteral l
prettyExp (Var n) = n
prettyExp (Lam args e) = 
  "fun " ++ prettyFunArgs args ++ " -> " ++ 
  parensIf (expPrec e < expPrec (Lam args e)) (prettyExp e)
prettyExp (TLam args e) = 
  "fun " ++ prettyFunArgs args ++ " -> " ++ 
  parensIf (expPrec e < expPrec (TLam args e)) (prettyExp e)
prettyExp (Clos env args e) = 
  "clos [" ++ prettyEnv env ++ "] " ++ prettyFunArgs args ++ " -> " ++ 
  parensIf (expPrec e < expPrec (Clos env args e)) (prettyExp e)
prettyExp (TClos env args e) = 
  "clos [" ++ prettyEnv env ++ "] " ++ prettyFunArgs args ++ " -> " ++ 
  parensIf (expPrec e < expPrec (TClos env args e)) (prettyExp e)
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
prettyExp (Mod m) = prettyModule m
prettyExp (BinOp op) = prettyBinOp op

prettyBinOp :: BinOp -> String
prettyBinOp (Add e1 e2) = prettyExp e1 ++ " + " ++ prettyExp e2
prettyBinOp (Sub e1 e2) = prettyExp e1 ++ " - " ++ prettyExp e2
prettyBinOp (Mul e1 e2) = prettyExp e1 ++ " * " ++ prettyExp e2

prettyLiteral :: Literal -> String
prettyLiteral (LitInt i) = show i
prettyLiteral (LitBool b) = if b then "true" else "false"
prettyLiteral (LitStr s) = show s