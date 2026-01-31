module Core.Pretty where

import Core.Syntax

parensIf :: Bool -> String -> String
parensIf True  s = "(" ++ s ++ ")"
parensIf False s = s

--------------------------------------------------------------------------------
-- Type Pretty Printing
--------------------------------------------------------------------------------

stringOfTyp :: Typ -> String
stringOfTyp (TyLit l) = case l of
    TyInt  -> "Int"
    TyBool -> "Bool"
    TyStr  -> "String"
stringOfTyp (TyVar n) = show n
stringOfTyp (TyArr t1 t2) =
    let s1 = parensIf (typPrec t1 <= typPrec (TyArr t1 t2)) (stringOfTyp t1)
        s2 = stringOfTyp t2
     in s1 ++ " -> " ++ s2
stringOfTyp (TyAll t) =
    let s = stringOfTyp t
     in "forall. " ++ s
stringOfTyp (TyBoxT bs t) =
    let sBinds = showTyEnv bs
        sTyp = parensIf (typPrec t < typPrec (TyBoxT bs t)) (stringOfTyp t)
     in "[" ++ sBinds ++ "] |> " ++ sTyp
stringOfTyp (TySubstT t1 t2) =
    let s1 = stringOfTyp t1
        s2 = parensIf (typPrec t2 < typPrec (TySubstT t1 t2)) (stringOfTyp t2)
     in "#[" ++ s1 ++ "]" ++ s2
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

--------------------------------------------------------------------------------
-- Environment Pretty Printing
--------------------------------------------------------------------------------

stringOfTyEnvE :: TyEnvE -> String
stringOfTyEnvE (Type t)   = stringOfTyp t
stringOfTyEnvE Kind       = "*"
stringOfTyEnvE (TypeEq t) = "eq " ++ stringOfTyp t

showTyEnv :: TyEnv -> String
showTyEnv = stringOfList stringOfTyEnvE . reverse

stringOfEnvE :: EnvE -> String
stringOfEnvE (ExpE e) = stringOfExp e
stringOfEnvE (TypE t) = "tdef " ++ stringOfTyp t

showEnv :: Env -> String
showEnv = stringOfList stringOfEnvE . reverse

stringOfList :: (a -> String) -> [a] -> String
stringOfList _ [] = ""
stringOfList f [x] = f x
stringOfList f (x:xs) = f x ++ ", " ++ stringOfList f xs

--------------------------------------------------------------------------------
-- Expression Pretty Printing
--------------------------------------------------------------------------------

stringOfLiteral :: Literal -> String
stringOfLiteral (LitInt n)  = show n
stringOfLiteral (LitBool b) = if b then "true" else "false"
stringOfLiteral (LitStr s)  = "\"" ++ s ++ "\""

stringOfExp :: Exp -> String
stringOfExp (Lit l) = stringOfLiteral l
stringOfExp (Var n) = "x" ++ show n
stringOfExp (Lam e) = "lam. " ++ stringOfExp e
stringOfExp (TLam e) = "Lam. " ++ stringOfExp e
stringOfExp (Fix e) = "fix " ++ parensIf (expPrec e < 2) (stringOfExp e)

stringOfExp (If e1 e2 e3) =
    "if " ++ stringOfExp e1 ++ " then " ++ stringOfExp e2 ++ " else " ++ stringOfExp e3

stringOfExp op@(Box env e) =
    let sEnv = showEnv env
        sE = parensIf (expPrec e < expPrec op) (stringOfExp e)
     in "[" ++ sEnv ++ "] |> " ++ sE

stringOfExp op@(App e1 e2) =
    let s1 = parensIf (expPrec e1 < expPrec op) (stringOfExp e1)
        s2 = parensIf (expPrec e2 <= expPrec op) (stringOfExp e2)
     in s1 ++ " " ++ s2
stringOfExp (BinOp binOp) = stringOfBinOp binOp
stringOfExp (Clos env e) =
    "<[" ++ showEnv env ++ "] | lam. " ++ stringOfExp e ++ ">"
stringOfExp (TClos env e) =
    "<[" ++ showEnv env ++ "] | Lam. " ++ stringOfExp e ++ ">"

stringOfExp op@(TApp e t) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExp e)
     in sE ++ " @ " ++ stringOfTyp t

stringOfExp (FEnv env) = "[" ++ showEnv env ++ "]"

stringOfExp (Rec label e) = "{" ++ label ++ " = " ++ stringOfExp e ++ "}"

stringOfExp op@(RProj e label) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExp e)
     in sE ++ "." ++ label

stringOfExp op@(Anno e t) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExp e)
     in sE ++ " : " ++ stringOfTyp t


stringOfBinOp :: BinOp -> String
stringOfBinOp op@(Add e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExp e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExp e2)
     in s1 ++ " + " ++ s2
stringOfBinOp op@(Sub e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExp e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExp e2)
     in s1 ++ " - " ++ s2
stringOfBinOp op@(Mul e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExp e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExp e2)
     in s1 ++ " * " ++ s2
stringOfBinOp op@(EqEq e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExp e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExp e2)
     in s1 ++ " == " ++ s2


-- | Precedence for Expressions
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

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

stringOfMaybeTyp :: Maybe Typ -> String
stringOfMaybeTyp Nothing = "None"
stringOfMaybeTyp (Just t) = stringOfTyp t

stringOfMaybeExp :: Maybe Exp -> String
stringOfMaybeExp Nothing = "None"
stringOfMaybeExp (Just e) = stringOfExp e
