{-# LANGUAGE InstanceSigs #-}

module EnvML.Syntax where

import qualified CoreFE.Syntax as CoreFE

type Name     = String            -- Alias for naming
type Imports  = [(Name, Typ)]     -- import x : A

type FunArgs = [(Name, FunArg)]
data FunArg
  = TyArg
  | TmArg
  | TmArgType Typ
  deriving (Show, Eq)

type TyCtx    = [TyCtxE]    -- [t : A, t1 : Type, type t2 = A]
data TyCtxE
  = TypeN    Name Typ       -- t : A
  | Type     Typ            -- nameless A  -- TODO: Currently unused
  | KindN    Name           -- t : *
  | Kind                    -- nameless * -- -- TODO: Currently unused
  | TypeEqN  Name Typ       -- type x = A !Must be named
  | TyMod    Name ModuleTyp -- module n : A
  | TypeEqM  Name ModuleTyp -- module type m = .. 
  deriving (Show, Eq)

data ModuleTyp
  = TyArrowM  Typ ModuleTyp   -- (A ->m I)
  | ForallM   Name ModuleTyp  -- ∀t. I
  | TySig     Intf            -- (sig .. end)
  | TyVarM    Name            -- M
  deriving (Show, Eq)

type Intf = [IntfE]                    -- (sig ... end) .eli
data IntfE
  = TyDef       Name Typ               -- (type t = ...)
  | ValDecl     Name Typ               -- (val x : t)
  | ModDecl     Name Typ               -- (module M : S)
  | FunctorDecl Name FunArgs Typ       -- (functor m (type t) (x: A) : S)
  | SigDecl     Name Intf              -- (module type S = ...)
  deriving (Show, Eq)

data Typ
  = TyLit     CoreFE.TyLit    -- int, bool, or string
  | TyVar     Name            -- x
  | TyArr     Typ   Typ       -- A -> B
  | TyAll     Name  Typ       -- forall a'. T
  | TyBoxT    TyCtx Typ       -- [t1 : int, t2 : int, t3: bool] ==> A
  | TyRcd     [(Name, Typ)]   -- {l1 : A1, l2 : A2, ln : An}
  | TySum     [(Name, Typ)] -- Tagged union: [(tag, field_type)]
  | TyMu      Name Typ      -- mu X. T (recursive type)
  | TyCtx     TyCtx           -- [t : A, t1 : Type, t2 : A=]
  | TyModule  ModuleTyp       -- Note: First-class modules
  | TyList    Typ             -- [A]
  deriving (Show, Eq)

data Module
  = VarM    Name
  | Functor FunArgs Module  -- functor (x : A) ->
  | Struct  Structures      -- struct type a = int; x = 1 end
  | MApp    Module Module   -- M1(M2)
  | MAppt   Module Typ      -- (M1 @A)
  | MAnno   Module ModuleTyp  -- (M1 ::m S)
  deriving (Show, Eq)

type Structures = [Structure]
data Structure
  = Let           Name (Maybe Typ) Exp  -- let x : A = e
  | TypDecl       Name Typ -- type t = A
  | ModTypDecl    Name ModuleTyp -- module type S = ...
  | ModStruct     Name (Maybe ModuleTyp) Module -- module M : S = struct ... endj
  | FunctStruct   Name FunArgs (Maybe ModuleTyp) Module  -- functor F (type t) (x : A) : S = struct ... end
  deriving (Eq, Show)

data CaseBranch
  = CaseBranch Name Name Exp
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

data Exp
  = Lit   CoreFE.Literal    -- Literals: int, double, bool, string
  | Var   Name              -- Var x, y, hello
  | Fix   Name Exp          -- fix f. e
  | If    Exp Exp Exp       -- if e1 then e2 else e3
  | Lam   FunArgs Exp       -- fun (x: A) (y : B) -> x + 1
  | Clos  Env FunArgs Exp   -- clos [type t = int, x = 1] (y: t) -> x + y
  | App   Exp Exp           -- f(x)
  | TClos Env FunArgs Exp   -- clos [type t = int, x = 1] ->
  | TApp  Exp Typ           -- f @t
  | Box   Env Exp           -- box [type t = int, x = 1] in e
  | Rec   [(Name, Exp)]     -- {l1 = e1, l2 = e2, l3 = e3}
  | RProj Exp Name          -- e.l
  | FEnv  Env               -- [type a = int, x = 1]
  | Anno  Exp Typ           -- (e::A)
  | Mod   Module            -- functor or struct
  | DataCon Name Exp Typ    -- Ctor(e) as T
  | Case Exp [CaseBranch]
  | Fold  Typ Exp            -- fold(e) as T
  | Unfold Exp               -- unfold(e)
  -- Lists
  | EList [Exp]             -- [e1, e2, e3]
  | ETake Int Exp           -- take(n, ls)
  -- Extensions
  | BinOp BinOp
  deriving (Show, Eq)

data BinOp
  = Add   Exp Exp
  | Sub   Exp Exp
  | Mul   Exp Exp
  | EqEq  Exp Exp
  | Neq   Exp Exp
  | Lt    Exp Exp
  | Le    Exp Exp
  | Gt    Exp Exp
  | Ge    Exp Exp
  deriving (Eq, Show)

type Precedence = Int

typPrec :: Typ -> Precedence
typPrec t = case t of
  TyLit _     -> 4
  TyVar _     -> 4
  TyRcd {}    -> 4
  TySum {}    -> 4
  TyMu _ _   -> 4
  TyCtx _     -> 4
  TyModule _  -> 4
  TyList _    -> 4
  TyArr _ _   -> 2
  TyBoxT _ _  -> 1
  TyAll _ _   -> 1

expPrec :: Exp -> Precedence
expPrec e = case e of
  Anno _ _  -> 0
  If {}     -> 1
  Box _ _   -> 1
  Clos {}   -> 1
  TClos {}  -> 1
  Fix _ _   -> 2
  Lam {}    -> 2
  App _ _   -> 3
  TApp _ _  -> 3
  RProj _ _ -> 3
  Lit _     -> 5
  Var _     -> 5
  Rec {}    -> 5
  FEnv _    -> 5
  Mod _     -> 5
  DataCon _ _ _ -> 5
  Case {}   -> 1
  Fold _ _  -> 3
  Unfold _  -> 3
  EList _   -> 5
  ETake _ _ -> 5
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

instance Pretty TyCtxE where
  pretty :: TyCtxE -> String
  pretty = prettyTyCtxE

instance Pretty IntfE where
  pretty :: IntfE -> String
  pretty = prettyIntfE

instance Pretty ModuleTyp where
  pretty :: ModuleTyp -> String
  pretty = prettyModuleTyp

instance Pretty Structure where
  pretty :: Structure -> String
  pretty = prettyStructure

parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s

intercalateComma :: [String] -> String
intercalateComma [] = ""
intercalateComma [x] = x
intercalateComma (x:xs) = x ++ ", " ++ intercalateComma xs

intercalateWith :: String -> [String] -> String
intercalateWith _ [] = ""
intercalateWith _ [x] = x
intercalateWith sep (x:xs) = x ++ sep ++ intercalateWith sep xs

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
prettyIntfE (ModDecl n mt) = "module " ++ n ++ " : " ++ prettyTyp mt
prettyIntfE (FunctorDecl n args mt) = 
  "functor " ++ n ++ " " ++ prettyFunArgs args ++ " : " ++ prettyTyp mt
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
  "forallm " ++ n ++ ". " ++ prettyModuleTyp m
prettyModuleTyp (TySig intf) = 
  "sig " ++ prettyIntf intf ++ " end"
prettyModuleTyp (TyVarM n) = n

-- Type pretty printing
prettyTyp :: Typ -> String
prettyTyp (TyLit l) = CoreFE.pretty l
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
prettyTyp (TySum ctors) =
  intercalateWith " | " (map prettyCtorSpec ctors)
prettyTyp (TyMu n t) = "mu " ++ n ++ ". " ++ prettyTyp t
prettyTyp (TyModule mt) = prettyModuleTyp mt
prettyTyp (TyList t) = "[" ++ prettyTyp t ++ "]"

prettyCtorSpec :: (Name, Typ) -> String
prettyCtorSpec (ctor, ty) = ctor ++ " as " ++ prettyTyp ty

prettyStructures :: Structures -> String
prettyStructures = concatMap (\s -> prettyStructure s ++ "\n")

-- Structures pretty printing
prettyStructure :: Structure -> String
prettyStructure (Let n Nothing e) = 
  "let " ++ n ++ " = " ++ prettyExp e
prettyStructure (Let n (Just t) e) = 
  "let " ++ n ++ " : " ++ prettyTyp t ++ " = " ++ prettyExp e
prettyStructure (TypDecl n t) = 
  "type " ++ n ++ " = " ++ prettyTyp t
prettyStructure (ModTypDecl n mt) = 
  "module type " ++ n ++ " = " ++ prettyModuleTyp mt
prettyStructure (ModStruct n Nothing s) = 
  "module " ++ n ++ " = " ++ prettyModule s
prettyStructure (ModStruct n (Just mt) s) = 
  "module " ++ n ++ " : " ++ prettyModuleTyp mt ++ " = " ++ prettyModule s
prettyStructure (FunctStruct n args Nothing s) = 
  "functor " ++ n ++ " " ++ prettyFunArgs args ++ " = " ++ prettyModule s
prettyStructure (FunctStruct n args (Just mt) s) = 
  "functor " ++ n ++ " " ++ prettyFunArgs args ++ " : " ++ prettyModuleTyp mt ++ " = " ++ prettyModule s

-- Module pretty printing
prettyModule :: Module -> String
prettyModule (VarM n) = n
prettyModule (Functor args m) =
  "functor " ++ prettyFunArgs args ++ " -> " ++ prettyModule m
prettyModule (Struct structs) =
  "struct " ++ prettyStructures structs ++ " end"
prettyModule (MApp m1 m2) = 
  prettyModule m1 ++ "(|" ++ prettyModule m2 ++ "|)"
prettyModule (MAppt m t) = 
  prettyModule m ++ " @m " ++ prettyTyp t
prettyModule (MAnno m1 mty) =
  "(" ++ prettyModule m1 ++ " :: " ++ prettyModuleTyp mty ++ ")"

-- Expression pretty printing
prettyExp :: Exp -> String
prettyExp (Lit l) = CoreFE.pretty l
prettyExp (Var n) = n
prettyExp (Fix n e) =
  "fix " ++ n ++ ". " ++ parensIf (expPrec e < expPrec (Fix n e)) (prettyExp e)
prettyExp (If e1 e2 e3) =
  "if " ++ prettyExp e1 ++ " then " ++ prettyExp e2 ++ " else " ++ prettyExp e3
prettyExp (Lam args e) = 
  "fun " ++ prettyFunArgs args ++ " -> " ++ 
  parensIf (expPrec e < expPrec (Lam args e)) (prettyExp e)
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
  " @" ++ prettyTyp t
prettyExp (Box env e) = 
  "box [" ++ prettyEnv env ++ "] in " ++ 
  parensIf (expPrec e < expPrec (Box env e)) (prettyExp e)
prettyExp (Rec []) = "{}"
prettyExp (Rec fields) = 
  "{" ++ intercalateComma (map (\(l, e) -> l ++ " = " ++ prettyExp e) fields) ++ "}"
prettyExp (RProj e label) = 
  parensIf (expPrec e < expPrec (RProj e label)) (prettyExp e) ++ "." ++ label
prettyExp (FEnv env) = "[" ++ prettyEnv env ++ "]"
prettyExp (Anno e t) = 
  parensIf (expPrec e < expPrec (Anno e t)) (prettyExp e) ++ " :: " ++ prettyTyp t
prettyExp (Mod m) = prettyModule m
prettyExp (DataCon ctor arg ty) = ctor ++ "(" ++ prettyExp arg ++ ") as " ++ prettyTyp ty
prettyExp (Fold t e) = "fold(" ++ prettyExp e ++ ") as " ++ prettyTyp t
prettyExp (Unfold e) = "unfold(" ++ prettyExp e ++ ")"
prettyExp (Case e branches) =
  "case " ++ prettyExp e ++ " of " ++ intercalateWith " " (map (("| " ++) . prettyCaseBranch) branches)
prettyExp (EList []) = "List[]"
prettyExp (EList es) = "List[" ++ intercalateComma (map prettyExp es) ++ "]"
prettyExp (ETake n ls) = "take(" ++ show n ++ ", " ++ prettyExp ls ++ ")"
prettyExp (BinOp (Add e1 e2)) = prettyExp e1 ++ " + " ++ prettyExp e2
prettyExp (BinOp (Sub e1 e2)) = prettyExp e1 ++ " - " ++ prettyExp e2
prettyExp (BinOp (Mul e1 e2)) = prettyExp e1 ++ " * " ++ prettyExp e2
prettyExp (BinOp (EqEq e1 e2)) = prettyExp e1 ++ " == " ++ prettyExp e2
prettyExp (BinOp (Neq e1 e2)) = prettyExp e1 ++ " != " ++ prettyExp e2
prettyExp (BinOp (Lt e1 e2)) = prettyExp e1 ++ " < " ++ prettyExp e2
prettyExp (BinOp (Le e1 e2)) = prettyExp e1 ++ " <= " ++ prettyExp e2
prettyExp (BinOp (Gt e1 e2)) = prettyExp e1 ++ " > " ++ prettyExp e2
prettyExp (BinOp (Ge e1 e2)) = prettyExp e1 ++ " >= " ++ prettyExp e2

prettyCaseBranch :: CaseBranch -> String
prettyCaseBranch (CaseBranch "_" "" body) =
  "_ => " ++ prettyExp body
prettyCaseBranch (CaseBranch ctor binder body) =
  "<" ++ ctor ++ "=" ++ binder ++ "> => " ++ prettyExp body