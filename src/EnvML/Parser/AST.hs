{-# LANGUAGE InstanceSigs #-}

module EnvML.Parser.AST where

main :: IO ()
main = print "EnvML Parsed AST"

-- AST with names and direct source-level representation

type Name = String

type TyEnv = [(Name, TyEnvE)] -- [t : A, t1 : Type, t2 : A=]

type Imports = [(Name, Typ)] -- import x : A

data TyEnvE
  = Type Typ -- A
  | Kind -- Type
  | TypeEq Typ -- A=
  deriving (Show, Eq)

data ModuleTyp
  = TyArrowM Typ ModuleTyp -- (A ->m I)
  | TySig Intf -- (sig .. end)
  deriving (Show, Eq)

type Intf = [IntfE] -- (sig ... end) .eli

data IntfE
  = TyDef Name Typ -- (type t = ...)
  | ValDecl Name Typ -- (val x : t)
  | ModDecl Name Typ -- (module M : S)
  | SigDecl Name Typ -- (module type S = ...)
  deriving (Show, Eq)

data Typ
  = TyLit TyLit -- int, bool, or string
  | TyVar Name -- a
  | TyArr Typ Typ -- A -> B
  | TyAll Name Typ -- forall a'. T
  | TyBoxT TyEnv Typ -- [t1 : int, t2 : int, t3: bool] ==> A
  | TyRcd String Typ -- {l : A}
  | TyEnvt TyEnv -- [t : A, t1 : Type, t2 : A=]
  | TyModule ModuleTyp -- Note: First-class modules
  deriving (Show, Eq)

data TyLit
  = TyInt -- int
  | TyBool -- bool
  | TyStr -- string
  deriving (Show, Eq)

-- Environment
type Env = [(Name, EnvE)]

-- Environment elements
data EnvE
  = ExpE Exp
  | TypE Typ
  | ModExpE Exp
  | ModTypE Typ
  deriving (Show, Eq)

data Module
  = VarM Name -- module variable
  | Functor FunArgs Module -- functor (x : A) ->
  | Struct Imports Env -- struct type a = int; x = 1 end
  | MApp Module Module -- M1 ^ M2
  | MAppt Module Typ -- M1 ^ @A
  | MLink Module Module -- link(M1, M2)
  deriving (Show, Eq)

data Exp
  = Lit Literal -- Literals: int, double, bool, string
  | Var Name -- Var x, y, hello
  | Lam FunArgs Exp -- fun (x: A) (y : B) -> x + 1
  | Clos Env Name Exp -- clos [type t = int, x = 1] (y: t) -> x + y
  | App Exp Exp -- f(x)
  | TClos Env Name Exp -- clos [type t = int, x = 1] ->
  | TApp Exp Typ -- f<t>
  | Box Env Exp -- box [type t = int, x = 1] in e
  | Rec Name Exp -- {l = A}
  | RProj Exp Name -- e.l
  | FEnv Env -- [type a = int, x = 1]
  | Anno Exp Typ -- (e::A)
  | ModE Module -- functor or struct
  -- Extensions
  | BinOp BinOp
  deriving (Show, Eq)

type FunArgs = [(Name, FunArg)]

data FunArg
  = TyArg
  | TmArg
  deriving (Show, Eq)

data BinOp
  = Add Exp Exp
  | Sub Exp Exp
  | Mul Exp Exp
  deriving (Show, Eq)

data Literal
  = LitInt Int -- 1, 2, etc.
  | LitBool Bool -- false, true
  | LitStr String -- "hello"
  deriving (Show, Eq)

type Precedence = Int

typPrec :: Typ -> Precedence
typPrec t = case t of
  TyLit _ -> 4
  TyVar _ -> 4
  TyRcd _ _ -> 4
  TyEnvt _ -> 4
  TyModule _ -> 4
  TyArr _ _ -> 2
  TyBoxT _ _ -> 1
  TyAll _ _ -> 1

expPrec :: Exp -> Precedence
expPrec e = case e of
  Anno _ _ -> 0
  Box _ _ -> 1
  Clos {} -> 1
  TClos {} -> 1
  Lam {} -> 2
  App _ _ -> 3
  TApp _ _ -> 3
  RProj _ _ -> 3
  Lit _ -> 5
  Var _ -> 5
  Rec _ _ -> 5
  FEnv _ -> 5
  ModE _ -> 5
  _ -> 4 -- TODO: Extensions

parensIf :: Bool -> String -> String
parensIf True s  = "(" ++ s ++ ")"
parensIf False s = s

prettyTyBind :: (Name, TyEnvE) -> String
prettyTyBind (n, Type t)   = n ++ " : " ++ prettyTyp t
prettyTyBind (n, Kind)     = n ++ " : Type"
prettyTyBind (n, TypeEq t) = n ++ " = " ++ prettyTyp t

prettyEnvBind :: (Name, EnvE) -> String
prettyEnvBind (n, ExpE e)    = n ++ " = " ++ prettyExp e
prettyEnvBind (n, TypE t)    = "type " ++ n ++ " = " ++ prettyTyp t
prettyEnvBind (n, ModExpE e) = "module " ++ n ++ " = " ++ prettyExp e
prettyEnvBind (n, ModTypE t)= "module type " ++ n ++ " = " ++ prettyTyp t

prettyEnv :: Env -> String
prettyEnv []     = ""
prettyEnv [b]    = prettyEnvBind b
prettyEnv (b:bs) = prettyEnvBind b ++ ", " ++ prettyEnv bs

prettyIntf :: Intf -> String
prettyIntf []     = ""
prettyIntf [e]    = prettyIntfE e
prettyIntf (e:es) = prettyIntfE e ++ "; " ++ prettyIntf es

prettyFunArgs :: FunArgs -> String
prettyFunArgs [] = ""
prettyFunArgs [arg] = "(" ++ prettyFunArg arg ++ ")"
prettyFunArgs (arg:args) = "(" ++ prettyFunArg arg ++ ") " ++ prettyFunArgs args

prettyFunArg :: (Name, FunArg) -> String
prettyFunArg (n, TyArg) = n ++ " : Type"
prettyFunArg (n, TmArg) = n

prettyModuleTyp :: ModuleTyp -> String
prettyModuleTyp (TyArrowM t m) = "(" ++ prettyTyp t ++ " ->m " ++ prettyModuleTyp m ++ ")"
prettyModuleTyp (TySig mt)     = "sig " ++ prettyIntf mt ++ " end"

prettyTyEnv :: TyEnv -> String
prettyTyEnv []     = ""
prettyTyEnv [b]    = prettyTyBind b
prettyTyEnv (b:bs) = prettyTyBind b ++ ", " ++ prettyTyEnv bs

prettyTyEnvE :: TyEnvE -> String
prettyTyEnvE (Type t)   = prettyTyp t
prettyTyEnvE Kind       = "Type"
prettyTyEnvE (TypeEq t) = "(" ++ prettyTyp t ++ ") ="

prettyIntfE :: IntfE -> String
prettyIntfE (TyDef n t)   = "type " ++ n ++ " = " ++ prettyTyp t
prettyIntfE (ValDecl n t) = "val " ++ n ++ " : " ++ prettyTyp t
prettyIntfE (ModDecl n mt) = "module " ++ n ++ " : " ++ prettyTyp mt
prettyIntfE (SigDecl n mt)= "module type " ++ n ++ " = " ++ prettyTyp mt

prettyTyp :: Typ -> String
prettyTyp (TyLit l) = prettyTyLit l
prettyTyp (TyVar s) = s
prettyTyp (TyArr t1 t2) =
  let s1 = parensIf (typPrec t1 < typPrec (TyArr t1 t2)) (prettyTyp t1)
      s2 = prettyTyp t2
   in "(" ++ s1 ++ " -> " ++ s2 ++ ")"
prettyTyp (TyAll x t) =
  let s = parensIf (typPrec t < typPrec (TyAll x t)) (prettyTyp t)
   in "forall " ++ x ++ ". " ++ s
prettyTyp (TyBoxT bs t) =
  let sBinds = prettyTyEnv bs
      sTyp   = parensIf (typPrec t < typPrec (TyBoxT bs t)) (prettyTyp t)
   in "[" ++ sBinds ++ "] ===> " ++ sTyp
prettyTyp (TyEnvt bs) = "[" ++ prettyTyEnv bs ++ "]"
prettyTyp (TyRcd label t) = "{" ++ label ++ " : " ++ prettyTyp t ++ "}"
prettyTyp (TyModule mt) = prettyModuleTyp mt

prettyTyLit :: TyLit -> String
prettyTyLit TyInt  = "int"
prettyTyLit TyBool = "bool"
prettyTyLit TyStr  = "string"

prettyModule :: Module -> String
prettyModule (Functor args e) =
  "functor " ++ prettyFunArgs args ++ " -> " ++ prettyModule e
prettyModule (Struct imports env) =
  let sEnv = prettyEnv env
      sImports = concatMap (\(n,t) -> "import " ++ n ++ " : " ++ prettyTyp t ++ "; ") imports
   in "struct " ++ sImports ++ sEnv ++ " end"
prettyModule (MApp m1 m2) = prettyModule m1 ++ " ^ " ++ prettyModule m2
prettyModule (MLink m1 m2) = "link(" ++ prettyModule m1 ++ ", " ++ prettyModule m2 ++ ")"
prettyModule (MAppt m t) = prettyModule m ++ " ^@ " ++ prettyTyp t
prettyModule (VarM n) = n

prettyExp :: Exp -> String
prettyExp (Lit l) = prettyLiteral l
prettyExp (Var n) = n
prettyExp (Lam args e) = "fun " ++ prettyFunArgs args ++ " -> " ++ parensIf (expPrec e < expPrec (Lam args e)) (prettyExp e)
prettyExp (Box env e) = "box [" ++ prettyEnv env ++ "] in " ++ parensIf (expPrec e < expPrec (Box env e)) (prettyExp e)
prettyExp (App e1 e2) = parensIf (expPrec e1 < expPrec (App e1 e2)) (prettyExp e1) ++ "(" ++ prettyExp e2 ++ ")"
prettyExp (Clos cetList n e) = "clos [" ++ prettyEnv cetList ++ "] (" ++ n ++ ") -> " ++ parensIf (expPrec e < expPrec (Clos cetList n e)) (prettyExp e)
prettyExp (TClos cetList n e) = "clos [" ++ prettyEnv cetList ++ "] type " ++ n ++ " -> " ++ parensIf (expPrec e < expPrec (TClos cetList n e)) (prettyExp e)
prettyExp (TApp e t) = parensIf (expPrec e < expPrec (TApp e t)) (prettyExp e) ++ "<" ++ prettyTyp t ++ ">"
prettyExp (FEnv env) = "[" ++ prettyEnv env ++ "]"
prettyExp (Rec label e) = "{" ++ label ++ " = " ++ prettyExp e ++ "}"
prettyExp (RProj e label) = parensIf (expPrec e < expPrec (RProj e label)) (prettyExp e) ++ "." ++ label
prettyExp (Anno e t) = parensIf (expPrec e < expPrec (Anno e t)) (prettyExp e) ++ " :: " ++ prettyTyp t
prettyExp (ModE m) = prettyModule m
prettyExp (BinOp op) = prettyBinOp op

prettyBinOp :: BinOp -> String
prettyBinOp (Add e1 e2) = prettyExp e1 ++ " + " ++ prettyExp e2
prettyBinOp (Sub e1 e2) = prettyExp e1 ++ " - " ++ prettyExp e2
prettyBinOp _ = "<binop> not implemented"

prettyLiteral :: Literal -> String
prettyLiteral (LitInt i) = show i
prettyLiteral (LitBool b) = if b then "true" else "false"
prettyLiteral (LitStr s) = show s
