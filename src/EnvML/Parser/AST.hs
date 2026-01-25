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
  deriving (Eq)

data ModuleTyp
  = TyArrowM Typ ModuleTyp -- (A ->m I)
  | TySig Intf -- (sig .. end)
  deriving (Eq)

type Intf = [IntfE] -- (sig ... end) .eli

data IntfE
  = TyDef Name Typ -- (type t = ...)
  | ValDecl Name Typ -- (val x : t)
  | ModDecl Name Name -- (module M : S)
  | SigDecl Name ModuleTyp -- (module type S = ...)
  deriving (Eq)

data Typ
  = TyLit TyLit -- int, bool, or string
  | TyVar Name -- a
  | TyArr Typ Typ -- A -> B
  | TyAll Name Typ -- forall a'. T
  | TyBoxT TyEnv Typ -- [t1 : int, t2 : int, t3: bool] ==> A
  | TyRcd String Typ -- {l : A}
  | TyEnvt TyEnv -- [t : A, t1 : Type, t2 : A=]
  | TyModule ModuleTyp -- Note: First-class modules
  deriving (Eq)

data TyLit
  = TyInt -- int
  | TyBool -- bool
  | TyStr -- string
  deriving (Eq)

-- Environment
type Env = [(Name, EnvE)]

-- Environment elements
data EnvE
  = ExpE Exp
  | TypE Typ
  deriving (Eq)

data Module
  = Functor Name Typ Module -- functor (x : A) ->
  | Struct Imports Env -- struct type a = int; x = 1 end
  | MApp Module Module -- M1 M2
  | MLink Module Module -- M1 |><| M2
  deriving (Eq)

data Exp
  = Lit Literal -- Literals: int, double, bool, string
  | Var Name -- Var x, y, hello
  | Lam Name Exp -- fun (x: A) -> x + 1
  | Clos Env Name Exp -- clos [type t = int, x = 1] (y: t) -> x + y
  | App Exp Exp -- f(x)
  | TLam Name Exp -- fun type a' -> fun (x: a') -> x
  | TClos Env Name Exp -- clos [type t = int, x = 1] ->
  | TApp Exp Typ -- f<t>
  | Box Env Exp -- box [type t = int, x = 1] in e
  | Rec Name Exp -- {l = A}
  | RProj Exp Name -- e.l
  | FEnv Env -- [type a = int, x = 1]
  | Anno Exp Typ -- (e::A)
  | ModE Module -- functor or struct
  deriving (Eq)

data Literal
  = LitInt Int -- 1, 2, etc.
  | LitBool Bool -- false, true
  | LitStr String -- "hello"
  deriving (Eq)

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
  TLam {} -> 2
  App _ _ -> 3
  TApp _ _ -> 3
  RProj _ _ -> 3
  Lit _ -> 5
  Var _ -> 5
  Rec _ _ -> 5
  FEnv _ -> 5
  ModE _ -> 5

parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s

parens :: Bool -> String -> String
parens True s = "(" ++ s ++ ")"
parens _ s = s

showTyBind :: (Name, TyEnvE) -> String
showTyBind (n, Type t) = n ++ " : " ++ show t
showTyBind (n, Kind) = n ++ " : Type"
showTyBind (n, TypeEq t) = n ++ " = " ++ show t

showEnvBind :: (Name, EnvE) -> String
showEnvBind (n, ExpE e) = n ++ " = " ++ show e
showEnvBind (n, TypE t) = "type " ++ n ++ " = " ++ show t

showEnv :: Env -> String
showEnv [] = ""
showEnv [b] = showEnvBind b
showEnv (b : bs) = showEnvBind b ++ ", " ++ showEnv bs

showIntf :: Intf -> String
showIntf [] = ""
showIntf [e] = show e
showIntf (e : es) = show e ++ "; " ++ showIntf es

instance Show ModuleTyp where
  show :: ModuleTyp -> String
  show (TyArrowM t m) =
    let sT = show t
        sM = show m
     in "(" ++ sT ++ " ->m " ++ sM ++ ")"
  show (TySig mt) =
    let sIntf = showIntf mt
     in "sig " ++ sIntf ++ " end"

showTyEnv :: TyEnv -> String
showTyEnv [] = ""
showTyEnv [b] = showTyBind b
showTyEnv (b : bs) = showTyBind b ++ ", " ++ showTyEnv bs

instance Show TyEnvE where
  show :: TyEnvE -> String
  show (Type t) = show t
  show Kind = "Type"
  show (TypeEq t) = "(" ++ show t ++ ")="

instance Show IntfE where
  show :: IntfE -> String
  show (TyDef n t) = "type " ++ n ++ " = " ++ show t
  show (ValDecl n t) = "val " ++ n ++ " :  " ++ show t
  show (ModDecl n1 n2) = "module " ++ n1 ++ " :  " ++ n2
  show (SigDecl n mt) = "module type " ++ n ++ " = " ++ show mt

instance Show Typ where
  show :: Typ -> String
  show (TyLit l) = show l
  show (TyVar s) = s
  show (TyArr t1 t2) =
    let s1 = parensIf (typPrec t1 < typPrec (TyArr t1 t2)) (show t1)
        s2 = show t2
     in "(" ++ s1 ++ " -> " ++ s2 ++ ")"
  show (TyAll x t) =
    let s = parensIf (typPrec t < typPrec (TyAll x t)) (show t)
     in "forall " ++ x ++ ". " ++ s
  show (TyBoxT bs t) =
    let sBinds = showTyEnv bs
        sTyp = parensIf (typPrec t < typPrec (TyBoxT bs t)) (show t)
     in "[" ++ sBinds ++ "] ===> " ++ sTyp
  show (TyEnvt bs) = "[" ++ showTyEnv bs ++ "]"
  show (TyRcd label t) = "{" ++ label ++ " : " ++ show t ++ "}"
  show (TyModule mt) = show mt

instance Show TyLit where
  show :: TyLit -> String
  show TyInt = "int"
  show TyBool = "bool"
  show TyStr = "string"

instance Show Module where
  show :: Module -> String
  show (Functor n t m) =
    let sT = show t
        sM = show m
     in "functor (" ++ n ++ " : " ++ sT ++ ") " ++ sM
  show (Struct imports env) =
    let sEnv = showEnv env
        showImport (n, t) = "import " ++ n ++ " : " ++ show t ++ "; "
        sImports = concatMap showImport imports
     in "struct " ++ sImports ++ sEnv ++ " end"
  show (MApp m1 m2) =
    let sM1 = show m1
        sM2 = show m2
     in "(" ++ sM1 ++ ") (" ++ sM2 ++ ")"
  show (MLink m1 m2) =
    let sM1 = show m1
        sM2 = show m2
     in "(" ++ sM1 ++ ") |><| (" ++ sM2 ++ ")"

instance Show Exp where
  show :: Exp -> String
  show (Lit l) = show l
  show (Var n) = n
  show (Lam n e) =
    let sE = show e
     in "fun (" ++ n ++ ") -> " ++ sE
  show (Box env e) =
    let sCets = showEnv env
        sE = parensIf (expPrec e < expPrec (Box env e)) (show e)
     in "box [" ++ sCets ++ "] in " ++ sE
  show (App e1 e2) =
    let s1 = parensIf (expPrec e1 < expPrec (App e1 e2)) (show e1)
        s2 = show e2
     in s1 ++ "(" ++ s2 ++ ")"
  show (TLam n e) =
    let sE = show e
     in "fun type " ++ n ++ " -> " ++ sE
  show (Clos cetList n e) =
    let sCets = showEnv cetList
        sE = parensIf (expPrec e < expPrec (Clos cetList n e)) (show e)
     in "clos [" ++ sCets ++ "] (" ++ n ++ ") -> " ++ sE
  show (TClos cetList n e) =
    let sCets = showEnv cetList
        sE = parensIf (expPrec e < expPrec (TClos cetList n e)) (show e)
     in "clos [" ++ sCets ++ "] type " ++ n ++ "-> " ++ sE
  show (TApp e t) =
    let sE = parensIf (expPrec e < expPrec (TApp e t)) (show e)
        sT = show t
     in sE ++ "<" ++ sT ++ ">"
  show (FEnv env) =
    let sEnv = showEnv env
     in "[" ++ sEnv ++ "]"
  show (Rec label e) =
    let sE = show e
     in "{" ++ label ++ " = " ++ sE ++ "}"
  show (RProj e label) =
    let sE = parensIf (expPrec e < expPrec (RProj e label)) (show e)
     in sE ++ "." ++ label
  show (Anno e t) =
    let sE = parensIf (expPrec e < expPrec (Anno e t)) (show e)
        sT = show t
     in sE ++ " :: " ++ sT
  show (ModE m) = show m

instance Show Literal where
  show :: Literal -> String
  show (LitInt i) = show i
  show (LitBool b) = if b then "true" else "false"
  show (LitStr s) = show s
