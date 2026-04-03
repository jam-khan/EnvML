module EnvML.Desugared where

import EnvML.Syntax (Name, Typ(..), ModuleTyp(..), FunArg(..))
import qualified EnvML.Syntax as Src
import qualified CoreFE.Syntax as CoreFE

data Module
  = VarM    Name
  | Functor Name FunArg Module  -- single-arg functor
  | Struct  Structures
  | MApp    Module Module
  | MAppt   Module Typ
  | MAnno   Module ModuleTyp
  deriving (Show, Eq)

type Structures = [Structure]
data Structure
  = Let       Name (Maybe Typ) Exp
  | TypDecl   Name Typ
  | ModTypDecl Name ModuleTyp
  | ModStruct  Name (Maybe ModuleTyp) Module
  -- FunctStruct is desugared into ModStruct + nested Functor
  deriving (Eq, Show)

data CaseBranch = CaseBranch Name Name Exp
  deriving (Show, Eq)

type Env = [EnvE]
data EnvE
  = ExpEN   Name Exp
  | ExpE    Exp
  | TypEN   Name Typ
  | TypE    Typ
  | ModE    Name Module
  | ModTypE Name ModuleTyp
  deriving (Show, Eq)

-- | Desugared expression: single-arg Lam/TLam, closures without FunArgs
data Exp
  = Lit     CoreFE.Literal
  | Var     Name
  | Fix     Name Exp
  | If      Exp Exp Exp
  | Lam     Name (Maybe Typ) Exp -- single term arg
  | TLam    Name Exp          -- single type arg
  | Clos    Env Exp           -- body is already nested Lam/TLam
  | App     Exp Exp
  | TClos   Env Exp           -- body is already nested TLam
  | TApp    Exp Typ
  | Box     Env Exp
  | Rec     [(Name, Exp)]
  | RProj   Exp Name
  | FEnv    Env
  | Anno    Exp Typ
  | Mod     Module
  | DataCon Name Exp Typ
  | Case    Exp [CaseBranch]
  | Fold    Typ Exp
  | Unfold  Exp
  | EList   [Exp]
  | ETake   Int Exp
  | BinOp   BinOp
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

----------------------
-- Pretty Printing ---
----------------------

prettyExp :: Exp -> String
prettyExp (Lit l) = CoreFE.pretty l
prettyExp (Var n) = n
prettyExp (Fix n e) = "fix " ++ n ++ ". " ++ prettyExp e
prettyExp (If e1 e2 e3) =
  "if " ++ prettyExp e1 ++ " then " ++ prettyExp e2 ++ " else " ++ prettyExp e3
prettyExp (Lam n Nothing e) = "lam (" ++ n ++ ") -> " ++ prettyExp e
prettyExp (Lam n (Just t) e) = "lam (" ++ n ++ " : " ++ Src.prettyTyp t ++ ") -> " ++ prettyExp e
prettyExp (TLam n e) = "tlam (type " ++ n ++ ") -> " ++ prettyExp e
prettyExp (Clos env e) =
  "clos [" ++ prettyEnv env ++ "] " ++ prettyExp e
prettyExp (App e1 e2) = prettyExp e1 ++ "(" ++ prettyExp e2 ++ ")"
prettyExp (TClos env e) =
  "clos [" ++ prettyEnv env ++ "] " ++ prettyExp e
prettyExp (TApp e t) = prettyExp e ++ " @" ++ Src.prettyTyp t
prettyExp (Box env e) = "box [" ++ prettyEnv env ++ "] in " ++ prettyExp e
prettyExp (Rec []) = "{}"
prettyExp (Rec fields) =
  "{" ++ intercalateComma (map (\(l, e) -> l ++ " = " ++ prettyExp e) fields) ++ "}"
prettyExp (RProj e label) = prettyExp e ++ "." ++ label
prettyExp (FEnv env) = "[" ++ prettyEnv env ++ "]"
prettyExp (Anno e t) = prettyExp e ++ " :: " ++ Src.prettyTyp t
prettyExp (Mod m) = prettyModule m
prettyExp (DataCon ctor arg ty) = ctor ++ "(" ++ prettyExp arg ++ ") as " ++ Src.prettyTyp ty
prettyExp (Case e branches) =
  "case " ++ prettyExp e ++ " of " ++ unwords (map (("| " ++) . prettyCaseBranch) branches)
prettyExp (Fold t e) = "fold(" ++ prettyExp e ++ ") as " ++ Src.prettyTyp t
prettyExp (Unfold e) = "unfold(" ++ prettyExp e ++ ")"
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
prettyCaseBranch (CaseBranch "_" "" body) = "_ => " ++ prettyExp body
prettyCaseBranch (CaseBranch ctor binder body) =
  "<" ++ ctor ++ "=" ++ binder ++ "> => " ++ prettyExp body

prettyModule :: Module -> String
prettyModule (VarM n) = n
prettyModule (Functor n arg m) =
  "functor " ++ Src.prettyFunArg (n, arg) ++ " -> " ++ prettyModule m
prettyModule (Struct structs) =
  "struct " ++ prettyStructures structs ++ " end"
prettyModule (MApp m1 m2) = prettyModule m1 ++ "(|" ++ prettyModule m2 ++ "|)"
prettyModule (MAppt m t) = prettyModule m ++ " @m " ++ Src.prettyTyp t
prettyModule (MAnno m1 mty) =
  "(" ++ prettyModule m1 ++ " :: " ++ Src.prettyModuleTyp mty ++ ")"

prettyStructures :: Structures -> String
prettyStructures = concatMap (\s -> prettyStructure s ++ "\n")

prettyStructure :: Structure -> String
prettyStructure (Let n Nothing e) = "let " ++ n ++ " = " ++ prettyExp e
prettyStructure (Let n (Just t) e) =
  "let " ++ n ++ " : " ++ Src.prettyTyp t ++ " = " ++ prettyExp e
prettyStructure (TypDecl n t) = "type " ++ n ++ " = " ++ Src.prettyTyp t
prettyStructure (ModTypDecl n mt) =
  "module type " ++ n ++ " = " ++ Src.prettyModuleTyp mt
prettyStructure (ModStruct n Nothing s) =
  "module " ++ n ++ " = " ++ prettyModule s
prettyStructure (ModStruct n (Just mt) s) =
  "module " ++ n ++ " : " ++ Src.prettyModuleTyp mt ++ " = " ++ prettyModule s

prettyEnvE :: EnvE -> String
prettyEnvE (ExpEN n e) = n ++ " = " ++ prettyExp e
prettyEnvE (ExpE e) = prettyExp e
prettyEnvE (TypEN n t) = "type " ++ n ++ " = " ++ Src.prettyTyp t
prettyEnvE (TypE t) = Src.prettyTyp t
prettyEnvE (ModE n m) = "module " ++ n ++ " = " ++ prettyModule m
prettyEnvE (ModTypE n mt) = "module type " ++ n ++ " = " ++ Src.prettyModuleTyp mt

prettyEnv :: Env -> String
prettyEnv [] = ""
prettyEnv [e] = prettyEnvE e
prettyEnv (e : es) = prettyEnvE e ++ ", " ++ prettyEnv es

intercalateComma :: [String] -> String
intercalateComma [] = ""
intercalateComma [x] = x
intercalateComma (x:xs) = x ++ ", " ++ intercalateComma xs
