{-# LANGUAGE InstanceSigs #-}
module CoreFE.Named where

import qualified CoreFE.Syntax as Nameless

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
  | Fix   Name Exp
  | If    Exp Exp Exp
  | BinOp BinOp
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
  | Fold  Typ Exp
  | Unfold Exp
  | DataCon Name Exp
  | Case Exp [CaseBranch]
  -- List primitives
  | EList  [Exp]        -- [e1, e2, e3]
  | ETake  Int Exp      -- take(n, ls)
  deriving (Eq, Show)

data CaseBranch
  = CaseBranch Name Name Exp
  deriving (Eq, Show)

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
  | TyMu     Name Typ       -- μt. A
  | TyBoxT   TyEnv Typ      -- Γ ▷ A
  | TySubstT Name Typ Typ   -- [t = A] B
  | TyRcd    String Typ     -- {l : A}
  | TySum    [(String, Typ)]
  | TyEnvt   TyEnv          -- Γ
  | TyList   Typ            -- [A]
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

class Pretty a where
  pretty :: a -> String

instance Pretty Typ where
  pretty :: Typ -> String
  pretty = prettyTyp

instance Pretty Exp where
  pretty :: Exp -> String
  pretty = prettyExp

instance Pretty EnvE where
  pretty :: EnvE -> String
  pretty = prettyEnvE

instance Pretty TyEnvE where
  pretty :: TyEnvE -> String
  pretty = prettyTyEnvE

prettyTyp :: Typ -> String
prettyTyp (TyLit l) = prettyTyLit l
prettyTyp (TyVar n) = n
prettyTyp (TyArr t1 t2) =
    let s1 = parenIf (isArrowTyp t1) (prettyTyp t1)
        s2 = prettyTyp t2
    in s1 ++ " -> " ++ s2
prettyTyp (TyAll n t) = "forall " ++ n ++ ". " ++ prettyTyp t
prettyTyp (TyMu n t) = "mu " ++ n ++ ". " ++ prettyTyp t
prettyTyp (TyBoxT env t) =
    "[" ++ prettyTyEnv env ++ "] => " ++ prettyTyp t
prettyTyp (TySubstT n t1 t2) =
    "[" ++ n ++ " = " ++ prettyTyp t1 ++ "] " ++ prettyTyp t2
prettyTyp (TyRcd label t) = "{" ++ label ++ " : " ++ prettyTyp t ++ "}"
prettyTyp (TySum ctors) =
  let showCtor (tag, t) = tag ++ " : " ++ prettyTyp t
  in intercalate " | " (map showCtor ctors)
prettyTyp (TyEnvt env) = "Env[" ++ prettyTyEnv env ++ "]"
prettyTyp (TyList t) = "[" ++ prettyTyp t ++ "]"

prettyTyLit :: Nameless.TyLit -> String
prettyTyLit Nameless.TyInt  = "int"
prettyTyLit Nameless.TyBool = "bool"
prettyTyLit Nameless.TyStr  = "string"
prettyTyLit Nameless.TyUnit = "unit"

isArrowTyp :: Typ -> Bool
isArrowTyp (TyArr _ _) = True
isArrowTyp _ = False

prettyTyEnv :: TyEnv -> String
prettyTyEnv [] = ""
prettyTyEnv es = intercalate ", " $ map prettyTyEnvE es

prettyTyEnvE :: TyEnvE -> String
prettyTyEnvE (Type n t) = n ++ " : " ++ prettyTyp t
prettyTyEnvE (Kind n) = n ++ " : *"
prettyTyEnvE (TypeEq n t) = "type " ++ n ++ " = " ++ prettyTyp t

prettyExp :: Exp -> String
prettyExp (Lit l) = prettyLit l
prettyExp (Var n) = n
prettyExp (Fix n e) = "fix " ++ n ++ ". " ++ parenIf (needsParenExp e) (prettyExp e)
prettyExp (If e1 e2 e3) =
  "if " ++ prettyExp e1 ++ " then " ++ prettyExp e2 ++ " else " ++ prettyExp e3
prettyExp (BinOp (Add e1 e2)) = prettyExp e1 ++ " + " ++ prettyExp e2
prettyExp (BinOp (Sub e1 e2)) = prettyExp e1 ++ " - " ++ prettyExp e2
prettyExp (BinOp (Mul e1 e2)) = prettyExp e1 ++ " * " ++ prettyExp e2
prettyExp (BinOp (EqEq e1 e2)) = prettyExp e1 ++ " == " ++ prettyExp e2
prettyExp (BinOp (Neq e1 e2)) = prettyExp e1 ++ " != " ++ prettyExp e2
prettyExp (BinOp (Lt e1 e2)) = prettyExp e1 ++ " < " ++ prettyExp e2
prettyExp (BinOp (Le e1 e2)) = prettyExp e1 ++ " <= " ++ prettyExp e2
prettyExp (BinOp (Gt e1 e2)) = prettyExp e1 ++ " > " ++ prettyExp e2
prettyExp (BinOp (Ge e1 e2)) = prettyExp e1 ++ " >= " ++ prettyExp e2
prettyExp (Lam n e) = "λ" ++ n ++ ". " ++ prettyExp e
prettyExp (TLam n e) = "Λ" ++ n ++ ". " ++ prettyExp e
prettyExp (Clos env e) =
    "⟨[" ++ prettyEnv env ++ "] | " ++ prettyExp e ++ "⟩"
prettyExp (TClos env e) =
    "⟨[" ++ prettyEnv env ++ "] | " ++ prettyExp e ++ "⟩"
prettyExp (App e1 e2) =
    prettyExp e1 ++ "(" ++ prettyExp e2 ++ ")"
prettyExp (TApp e t) =
    prettyExp e ++ " @" ++ prettyTyp t
prettyExp (Box env e) =
    "[" ++ prettyEnv env ++ "] => " ++ prettyExp e
prettyExp (Rec label e) =
    "{" ++ label ++ " = " ++ prettyExp e ++ "}"
prettyExp (RProj e label) =
    parenIf (needsParenProj e) (prettyExp e) ++ "." ++ label
prettyExp (FEnv env) = "[" ++ prettyEnv env ++ "]"
prettyExp (Anno e t) =
    parenIf (needsParenExp e) (prettyExp e) ++ " : " ++ prettyTyp t
prettyExp (Fold t e) = "fold [" ++ prettyTyp t ++ "] " ++ prettyExp e
prettyExp (Unfold e) = "unfold " ++ prettyExp e
prettyExp (DataCon ctor arg) = ctor ++ "(" ++ prettyExp arg ++ ")"
prettyExp (Case e branches) =
  "case " ++ prettyExp e ++ " of " ++ intercalate " | " (map prettyCaseBranch branches)
prettyExp (EList []) = "List[]"
prettyExp (EList es) = "List[" ++ intercalate ", " (map prettyExp es) ++ "]"
prettyExp (ETake n ls) = "take(" ++ show n ++ ", " ++ prettyExp ls ++ ")"

needsParenExp :: Exp -> Bool
needsParenExp (App _ _) = True
needsParenExp (TApp _ _) = True
needsParenExp (Lam _ _) = True
needsParenExp (TLam _ _) = True
needsParenExp (Fix _ _) = True
needsParenExp (If _ _ _) = True
needsParenExp (BinOp _) = True
needsParenExp (Anno _ _) = True
needsParenExp (Fold _ _) = True
needsParenExp (Unfold _) = True
needsParenExp _ = False

needsParenProj :: Exp -> Bool
needsParenProj (Var _) = False
needsParenProj (RProj _ _) = False
needsParenProj (FEnv _) = False
needsParenProj (Rec _ _) = False
needsParenProj (DataCon _ _) = False
needsParenProj (EList _) = False
needsParenProj _ = True

prettyCaseBranch :: CaseBranch -> String
prettyCaseBranch (CaseBranch ctor binder body) =
  "<" ++ ctor ++ "=" ++ binder ++ "> => " ++ prettyExp body

prettyEnv :: Env -> String
prettyEnv [] = ""
prettyEnv es = intercalate ", " $ map prettyEnvE es

prettyEnvE :: EnvE -> String
prettyEnvE (ExpE n e) = n ++ " = " ++ prettyExp e
prettyEnvE (ModE n e) = n ++ " = " ++ prettyExp e
prettyEnvE (TypE n t) = "type " ++ n ++ " = " ++ prettyTyp t

prettyLit :: Nameless.Literal -> String
prettyLit (Nameless.LitInt n) = show n
prettyLit (Nameless.LitBool b) = if b then "true" else "false"
prettyLit (Nameless.LitStr s) = "\"" ++ s ++ "\""
prettyLit Nameless.LitUnit = "unit"


parenIf :: Bool -> String -> String
parenIf True s = "(" ++ s ++ ")"
parenIf False s = s

intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs