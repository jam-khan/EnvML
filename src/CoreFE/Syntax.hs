{-# LANGUAGE InstanceSigs #-}
module CoreFE.Syntax where

type TyEnv = [TyEnvE]

data TyEnvE
  = Type Typ
  | Kind
  | TypeEq Typ
  deriving (Eq, Show)

data Typ
  = TyLit TyLit
  | TyVar Int
  | TyArr Typ Typ
  | TyAll Typ
  | TyBoxT TyEnv Typ
  | TySubstT Typ Typ
  | TyRcd String Typ
  | TyEnvt TyEnv
  deriving (Eq, Show)

data TyLit
  = TyInt
  | TyBool
  | TyStr
  deriving (Eq, Show)

type Env = [EnvE]

data EnvE = ExpE Exp | TypE Typ
  deriving (Eq, Show)

data Exp
  = Lit   Literal
  | Var   Int
  | Lam   Exp
  | Clos  Env Exp
  | App   Exp Exp
  | TLam  Exp
  | TClos Env Exp
  | TApp  Exp Typ
  | Box   Env Exp
  | Rec   String Exp
  | RProj Exp String
  | FEnv  Env
  | Anno  Exp Typ
  | Fix   Exp
  | If    Exp Exp Exp
  | BinOp BinOp
  deriving (Eq, Show)

data BinOp
  = Add   Exp Exp
  | Sub   Exp Exp
  | Mul   Exp Exp
  | EqEq  Exp Exp
  deriving (Eq, Show)

data Literal
  = LitInt  Int
  | LitBool Bool
  | LitStr  String
  deriving (Eq, Show)


class Pretty a where
  pretty :: a -> String

-- Instances for CoreFE.Syntax types
instance Pretty Typ where
  pretty :: Typ -> String
  pretty = stringOfTyp

instance Pretty TyLit where
  pretty :: TyLit -> String
  pretty TyInt  = "Int"
  pretty TyBool = "Bool"
  pretty TyStr  = "String"

instance Pretty TyEnvE where
  pretty :: TyEnvE -> String
  pretty = stringOfTyEnvE

instance Pretty Exp where
  pretty :: Exp -> String
  pretty = prettyTop

instance Pretty Literal where
  pretty :: Literal -> String
  pretty = stringOfLiteral

instance Pretty BinOp where
  pretty :: BinOp -> String
  pretty = stringOfBinOp

instance Pretty EnvE where
  pretty :: EnvE -> String
  pretty = stringOfEnvE

prettyTop :: Exp -> String
prettyTop (FEnv env) = prettyEnvVertical 0 (reverse env)
prettyTop e = stringOfExpI 0 e

indent :: Int -> String
indent n = replicate (n * 2) ' '

prettyEnvVertical :: Int -> [EnvE] -> String
prettyEnvVertical _ [] = "[]"
prettyEnvVertical lvl entries =
  concatMap (\e -> indent lvl ++ stringOfEnvEI lvl e ++ "\n\n") entries

parensIf :: Bool -> String -> String
parensIf True  s = "(" ++ s ++ ")"
parensIf False s = s

stringOfTyp :: Typ -> String
stringOfTyp (TyLit l) = pretty l
stringOfTyp (TyVar n) = "t" ++ show n
stringOfTyp (TyArr t1 t2) =
    let s1 = parensIf (typPrec t1 <= typPrec (TyArr t1 t2)) (stringOfTyp t1)
        s2 = stringOfTyp t2
     in s1 ++ " → " ++ s2
stringOfTyp (TyAll t) =
    "∀. " ++ stringOfTyp t
stringOfTyp (TyBoxT bs t) =
    let sBinds = showTyEnv bs
        sTyp = parensIf (typPrec t < typPrec (TyBoxT bs t)) (stringOfTyp t)
     in "[" ++ sBinds ++ "] ▷ " ++ sTyp
stringOfTyp (TySubstT t1 t2) =
    let s1 = stringOfTyp t1
        s2 = parensIf (typPrec t2 < typPrec (TySubstT t1 t2)) (stringOfTyp t2)
     in "#[" ++ s1 ++ "] " ++ s2
stringOfTyp (TyEnvt bs) = "Env[" ++ showTyEnv bs ++ "]"
stringOfTyp (TyRcd label t) = "{" ++ label ++ " : " ++ stringOfTyp t ++ "}"

typPrec :: Typ -> Int
typPrec (TyLit _)      = 10
typPrec (TyVar _)      = 10
typPrec (TyRcd _ _)    = 10
typPrec (TyEnvt _)     = 10
typPrec (TySubstT _ _) = 8
typPrec (TyBoxT _ _)   = 8
typPrec (TyArr _ _)    = 4
typPrec (TyAll _)      = 2

stringOfTyEnvE :: TyEnvE -> String
stringOfTyEnvE (Type t)   = stringOfTyp t
stringOfTyEnvE Kind       = "★"
stringOfTyEnvE (TypeEq t) = "≡ " ++ stringOfTyp t

showTyEnv :: TyEnv -> String
showTyEnv = stringOfList stringOfTyEnvE . reverse

stringOfEnvE :: EnvE -> String
stringOfEnvE = stringOfEnvEI 0

stringOfEnvEI :: Int -> EnvE -> String
stringOfEnvEI lvl (ExpE e) = stringOfEnvExpI lvl e
stringOfEnvEI _   (TypE t) = "type " ++ stringOfTyp t

stringOfEnvExpI :: Int -> Exp -> String
stringOfEnvExpI lvl (Rec label e) =
    label ++ " = " ++ stringOfExpCompactI lvl e
stringOfEnvExpI lvl (Anno (Rec label e) t) =
    label ++ " : " ++ stringOfTyp t ++ " =\n"
    ++ indent (lvl + 1) ++ stringOfExpCompactI (lvl + 1) e
stringOfEnvExpI lvl (Anno e t) =
    stringOfExpCompactI lvl e ++ "\n"
    ++ indent (lvl + 1) ++ ": " ++ stringOfTyp t
stringOfEnvExpI lvl e = stringOfExpCompactI lvl e

stringOfExpCompactI :: Int -> Exp -> String
stringOfExpCompactI lvl e =
    let s = stringOfExpI lvl e
    in  s

stringOfExp :: Exp -> String
stringOfExp = stringOfExpI 0

stringOfExpI :: Int -> Exp -> String
stringOfExpI _ (Lit l) = stringOfLiteral l
stringOfExpI _ (Var n) = "x" ++ show n
stringOfExpI lvl (Lam e) =
    "λ. " ++ stringOfExpI lvl e
stringOfExpI lvl (TLam e) =
    "Λ. " ++ stringOfExpI lvl e
stringOfExpI lvl (Fix e) =
    "fix " ++ parensIf (expPrec e < 2) (stringOfExpI lvl e)

stringOfExpI lvl (If e1 e2 e3) =
    "if " ++ stringOfExpI lvl e1 ++ "\n"
    ++ indent (lvl + 1) ++ "then " ++ stringOfExpI (lvl + 1) e2 ++ "\n"
    ++ indent (lvl + 1) ++ "else " ++ stringOfExpI (lvl + 1) e3

stringOfExpI lvl op@(Box env e) =
    let sEnv = showEnvInline env
        sE = parensIf (expPrec e < expPrec op) (stringOfExpI lvl e)
     in "[" ++ sEnv ++ "] ▷ " ++ sE

stringOfExpI lvl op@(App e1 e2) =
    let s1 = parensIf (expPrec e1 < expPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= expPrec op) (stringOfExpI lvl e2)
     in s1 ++ " " ++ s2

stringOfExpI lvl (BinOp binOp) = stringOfBinOpI lvl binOp

stringOfExpI lvl (Clos env e) =
    "⟨[" ++ showEnvInline env ++ "] | λ. " ++ stringOfExpI lvl e ++ "⟩"

stringOfExpI lvl (TClos env e) =
    "⟨[" ++ showEnvInline env ++ "] | Λ. " ++ stringOfExpI lvl e ++ "⟩"

stringOfExpI lvl op@(TApp e t) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExpI lvl e)
     in sE ++ " @" ++ stringOfTyp t

stringOfExpI lvl (FEnv env) =
    let entries = reverse env
    in  if isSmallEnv entries
        then "[" ++ stringOfList stringOfEnvE entries ++ "]"
        else "[\n" ++ prettyEnvVertical (lvl + 1) entries ++ indent lvl ++ "]"

stringOfExpI _ (Rec label e) =
    "{" ++ label ++ " = " ++ stringOfExp e ++ "}"

stringOfExpI lvl op@(RProj e label) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExpI lvl e)
     in sE ++ "." ++ label

stringOfExpI lvl op@(Anno e t) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExpI lvl e)
     in sE ++ " : " ++ stringOfTyp t

-- Heuristic: an env is "small" if it has <= 2 entries and no nested FEnv
isSmallEnv :: [EnvE] -> Bool
isSmallEnv entries =
    length entries <= 2 && all isSimpleEnvE entries

isSimpleEnvE :: EnvE -> Bool
isSimpleEnvE (ExpE e) = isSimpleExp e
isSimpleEnvE (TypE _) = True

isSimpleExp :: Exp -> Bool
isSimpleExp (Lit _)     = True
isSimpleExp (Var _)     = True
isSimpleExp (Rec _ e)   = isSimpleExp e
isSimpleExp (RProj e _) = isSimpleExp e
isSimpleExp _           = False

showEnvInline :: Env -> String
showEnvInline = stringOfList stringOfEnvE . reverse

showEnv :: Env -> String
showEnv = showEnvInline

stringOfBinOp :: BinOp -> String
stringOfBinOp = stringOfBinOpI 0

stringOfBinOpI :: Int -> BinOp -> String
stringOfBinOpI lvl op@(Add e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " + " ++ s2
stringOfBinOpI lvl op@(Sub e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " - " ++ s2
stringOfBinOpI lvl op@(Mul e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " * " ++ s2
stringOfBinOpI lvl op@(EqEq e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " == " ++ s2

stringOfLiteral :: Literal -> String
stringOfLiteral (LitInt n)  = show n
stringOfLiteral (LitBool b) = if b then "true" else "false"
stringOfLiteral (LitStr s)  = "\"" ++ s ++ "\""

expPrec :: Exp -> Int
expPrec (Lit _)     = 10
expPrec (Var _)     = 10
expPrec (FEnv _)    = 10
expPrec (Rec _ _)   = 10
expPrec (RProj _ _) = 9
expPrec (App _ _)   = 8
expPrec (TApp _ _)  = 8
expPrec (BinOp _)   = 6
expPrec (Anno _ _)  = 4
expPrec (Box _ _)   = 3
expPrec (Clos _ _)  = 3
expPrec (TClos _ _) = 3
expPrec (If {})     = 2
expPrec (Fix _)     = 2
expPrec (Lam _)     = 1
expPrec (TLam _)    = 1

binOpPrec :: BinOp -> Int
binOpPrec (Mul _ _)  = 7
binOpPrec (Add _ _)  = 6
binOpPrec (Sub _ _)  = 6
binOpPrec (EqEq _ _) = 5

stringOfList :: (a -> String) -> [a] -> String
stringOfList _ [] = ""
stringOfList f [x] = f x
stringOfList f (x:xs) = f x ++ ", " ++ stringOfList f xs

stringOfMaybeTyp :: Maybe Typ -> String
stringOfMaybeTyp Nothing = "None"
stringOfMaybeTyp (Just t) = stringOfTyp t

stringOfMaybeExp :: Maybe Exp -> String
stringOfMaybeExp Nothing = "None"
stringOfMaybeExp (Just e) = stringOfExp e