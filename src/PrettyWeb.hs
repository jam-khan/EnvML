{-# LANGUAGE InstanceSigs #-}
module PrettyWeb where

import qualified EnvML.Syntax as EnvML
import qualified CoreFE.Named as Named
import qualified CoreFE.Syntax as CoreFE

--------------------------------------------------------------------------------
-- User-Friendly Pretty Printing for the Playground
-- 
-- This module provides clean, readable output for all three AST levels:
-- 1. EnvML Source AST
-- 2. CoreFE Named AST  
-- 3. CoreFE Nameless (De Bruijn) AST
--------------------------------------------------------------------------------

parenIf :: Bool -> String -> String
parenIf True s = "(" ++ s ++ ")"
parenIf False s = s

intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

indent :: Int -> String
indent n = replicate (n * 2) ' '

--------------------------------------------------------------------------------
-- EnvML Source AST - User Display
--------------------------------------------------------------------------------

prettyEnvMLModule :: EnvML.Module -> String
prettyEnvMLModule (EnvML.Struct structs) = 
    unlines $ map prettyEnvMLStructure structs
prettyEnvMLModule m = EnvML.pretty m

prettyEnvMLStructure :: EnvML.Structure -> String
prettyEnvMLStructure (EnvML.Let n Nothing e) = 
    "let " ++ n ++ " = " ++ prettyEnvMLExpShort e
prettyEnvMLStructure (EnvML.Let n (Just t) e) = 
    "let " ++ n ++ " : " ++ EnvML.prettyTyp t ++ " = " ++ prettyEnvMLExpShort e
prettyEnvMLStructure (EnvML.TypDecl n t) = 
    "type " ++ n ++ " = " ++ EnvML.prettyTyp t
prettyEnvMLStructure (EnvML.ModTypDecl n mt) = 
    "module type " ++ n ++ " = " ++ EnvML.prettyModuleTyp mt
prettyEnvMLStructure (EnvML.ModStruct n Nothing m) = 
    "module " ++ n ++ " = " ++ prettyEnvMLModuleShort m
prettyEnvMLStructure (EnvML.ModStruct n (Just mt) m) = 
    "module " ++ n ++ " : " ++ EnvML.prettyModuleTyp mt ++ " =\n  " ++ prettyEnvMLModuleShort m
prettyEnvMLStructure (EnvML.FunctStruct n args Nothing m) = 
    "module " ++ n ++ " " ++ EnvML.prettyFunArgs args ++ " = " ++ prettyEnvMLModuleShort m
prettyEnvMLStructure (EnvML.FunctStruct n args (Just mt) m) = 
    "module " ++ n ++ " " ++ EnvML.prettyFunArgs args ++ " : " ++ EnvML.prettyModuleTyp mt ++ " =\n  " ++ prettyEnvMLModuleShort m

prettyEnvMLModuleShort :: EnvML.Module -> String
prettyEnvMLModuleShort (EnvML.VarM n) = n
prettyEnvMLModuleShort (EnvML.Functor args _) = "functor " ++ EnvML.prettyFunArgs args ++ " -> ..."
prettyEnvMLModuleShort (EnvML.Struct _) = "struct ... end"
prettyEnvMLModuleShort (EnvML.MApp m1 m2) = prettyEnvMLModuleShort m1 ++ "(" ++ prettyEnvMLModuleShort m2 ++ ")"
prettyEnvMLModuleShort (EnvML.MAppt m t) = prettyEnvMLModuleShort m ++ " @" ++ EnvML.prettyTyp t
prettyEnvMLModuleShort (EnvML.MAnno m mt) = "(" ++ prettyEnvMLModuleShort m ++ " : " ++ EnvML.prettyModuleTyp mt ++ ")"

prettyEnvMLExpShort :: EnvML.Exp -> String
prettyEnvMLExpShort (EnvML.Lit l) = prettyLiteral l
prettyEnvMLExpShort (EnvML.Var n) = n
prettyEnvMLExpShort (EnvML.Lam args _) = "fun " ++ EnvML.prettyFunArgs args ++ " -> ..."
prettyEnvMLExpShort (EnvML.TLam args _) = "fun " ++ EnvML.prettyFunArgs args ++ " -> ..."
prettyEnvMLExpShort (EnvML.App e1 e2) = prettyEnvMLExpShort e1 ++ "(" ++ prettyEnvMLExpShort e2 ++ ")"
prettyEnvMLExpShort (EnvML.TApp e t) = prettyEnvMLExpShort e ++ " @" ++ EnvML.prettyTyp t
prettyEnvMLExpShort (EnvML.Box _ _) = "box [...] in ..."
prettyEnvMLExpShort (EnvML.Rec fields) = "{" ++ intercalate ", " (map fst fields) ++ "}"
prettyEnvMLExpShort (EnvML.RProj e l) = prettyEnvMLExpShort e ++ "." ++ l
prettyEnvMLExpShort (EnvML.Anno e t) = "(" ++ prettyEnvMLExpShort e ++ " : " ++ EnvML.prettyTyp t ++ ")"
prettyEnvMLExpShort (EnvML.Mod m) = prettyEnvMLModuleShort m
prettyEnvMLExpShort _ = "..."

--------------------------------------------------------------------------------
-- CoreFE Named AST - User Display
--------------------------------------------------------------------------------

prettyNamedModule :: Named.Exp -> String
prettyNamedModule (Named.FEnv env) = 
    unlines $ map prettyNamedBinding (reverse env)
prettyNamedModule e = Named.pretty e

prettyNamedBinding :: Named.EnvE -> String
prettyNamedBinding (Named.TypE n t) = 
    "type " ++ n ++ " = " ++ Named.prettyTyp t
prettyNamedBinding (Named.ModE n e) = prettyNamedBindingExp n e
prettyNamedBinding (Named.ExpE n e) = prettyNamedBindingExp n e

prettyNamedBindingExp :: Named.Name -> Named.Exp -> String
prettyNamedBindingExp name (Named.Anno e t) = 
    name ++ " : " ++ Named.prettyTyp t ++ " =\n  " ++ prettyNamedExpShort e
prettyNamedBindingExp name e = 
    name ++ " = " ++ prettyNamedExpShort e

prettyNamedExpShort :: Named.Exp -> String
prettyNamedExpShort (Named.Lit l) = prettyLiteral l
prettyNamedExpShort (Named.Var n) = n
prettyNamedExpShort (Named.Lam n _) = "λ" ++ n ++ ". ..."
prettyNamedExpShort (Named.TLam n _) = "Λ" ++ n ++ ". ..."
prettyNamedExpShort (Named.Clos _ _) = "<closure>"
prettyNamedExpShort (Named.TClos _ _) = "<type-closure>"
prettyNamedExpShort (Named.App e1 e2) = prettyNamedExpShort e1 ++ "(" ++ prettyNamedExpShort e2 ++ ")"
prettyNamedExpShort (Named.TApp e t) = prettyNamedExpShort e ++ " @" ++ Named.prettyTyp t
prettyNamedExpShort (Named.Box _ _) = "[...] => ..."
prettyNamedExpShort (Named.Rec l e) = "{" ++ l ++ " = " ++ prettyNamedExpShort e ++ "}"
prettyNamedExpShort (Named.RProj e l) = prettyNamedExpShort e ++ "." ++ l
prettyNamedExpShort (Named.FEnv env) = prettyNamedEnvShort env
prettyNamedExpShort (Named.Anno e _) = prettyNamedExpShort e

prettyNamedEnvShort :: Named.Env -> String
prettyNamedEnvShort [] = "[]"
prettyNamedEnvShort env 
    | length env <= 2 = "[" ++ intercalate ", " (map shortEntry env) ++ "]"
    | otherwise = "[" ++ intercalate ", " (map shortEntry (take 2 env)) ++ ", ...]"
  where
    shortEntry (Named.ExpE n _) = n
    shortEntry (Named.ModE n _) = n
    shortEntry (Named.TypE n _) = "type " ++ n

--------------------------------------------------------------------------------
-- CoreFE Nameless (De Bruijn) AST - User Display
--------------------------------------------------------------------------------

prettyDeBruijnModule :: CoreFE.Exp -> String
prettyDeBruijnModule (CoreFE.FEnv env) = 
    unlines $ map prettyDeBruijnBinding (reverse env)
prettyDeBruijnModule e = prettyDeBruijnExp e

prettyDeBruijnBinding :: CoreFE.EnvE -> String
prettyDeBruijnBinding (CoreFE.TypE t) = 
    "type " ++ prettyDeBruijnTyp t
prettyDeBruijnBinding (CoreFE.ExpE e) = prettyDeBruijnBindingExp e

prettyDeBruijnBindingExp :: CoreFE.Exp -> String
prettyDeBruijnBindingExp (CoreFE.Rec label (CoreFE.Anno e t)) =
    label ++ " : " ++ prettyDeBruijnTyp t ++ " =\n  " ++ prettyDeBruijnExpShort e
prettyDeBruijnBindingExp (CoreFE.Anno (CoreFE.Rec label e) t) =
    label ++ " : " ++ prettyDeBruijnTyp t ++ " =\n  " ++ prettyDeBruijnExpShort e
prettyDeBruijnBindingExp (CoreFE.Rec label e) =
    label ++ " = " ++ prettyDeBruijnExpShort e
prettyDeBruijnBindingExp e = prettyDeBruijnExpShort e

prettyDeBruijnExpShort :: CoreFE.Exp -> String
prettyDeBruijnExpShort (CoreFE.Lit l) = prettyLiteral l
prettyDeBruijnExpShort (CoreFE.Var n) = "x" ++ show n
prettyDeBruijnExpShort (CoreFE.Lam _) = "λ. ..."
prettyDeBruijnExpShort (CoreFE.TLam _) = "Λ. ..."
prettyDeBruijnExpShort (CoreFE.Clos _ _) = "<closure>"
prettyDeBruijnExpShort (CoreFE.TClos _ _) = "<type-closure>"
prettyDeBruijnExpShort (CoreFE.App e1 e2) = prettyDeBruijnExpShort e1 ++ " " ++ parenIf (needsParenCore e2) (prettyDeBruijnExpShort e2)
prettyDeBruijnExpShort (CoreFE.TApp e t) = prettyDeBruijnExpShort e ++ " @" ++ prettyDeBruijnTyp t
prettyDeBruijnExpShort (CoreFE.Box _ _) = "[...] => ..."
prettyDeBruijnExpShort (CoreFE.Rec l e) = "{" ++ l ++ " = " ++ prettyDeBruijnExpShort e ++ "}"
prettyDeBruijnExpShort (CoreFE.RProj e l) = prettyDeBruijnExpShort e ++ "." ++ l
prettyDeBruijnExpShort (CoreFE.FEnv env) = prettyDeBruijnEnvShort env
prettyDeBruijnExpShort (CoreFE.Anno e _) = prettyDeBruijnExpShort e
prettyDeBruijnExpShort (CoreFE.Fix _) = "fix ..."
prettyDeBruijnExpShort (CoreFE.If _ _ _) = "if ... then ... else ..."
prettyDeBruijnExpShort (CoreFE.BinOp op) = prettyDeBruijnBinOpShort op

prettyDeBruijnBinOpShort :: CoreFE.BinOp -> String
prettyDeBruijnBinOpShort (CoreFE.Add e1 e2) = prettyDeBruijnExpShort e1 ++ " + " ++ prettyDeBruijnExpShort e2
prettyDeBruijnBinOpShort (CoreFE.Sub e1 e2) = prettyDeBruijnExpShort e1 ++ " - " ++ prettyDeBruijnExpShort e2
prettyDeBruijnBinOpShort (CoreFE.Mul e1 e2) = prettyDeBruijnExpShort e1 ++ " * " ++ prettyDeBruijnExpShort e2
prettyDeBruijnBinOpShort (CoreFE.EqEq e1 e2) = prettyDeBruijnExpShort e1 ++ " == " ++ prettyDeBruijnExpShort e2

prettyDeBruijnEnvShort :: CoreFE.Env -> String
prettyDeBruijnEnvShort [] = "[]"
prettyDeBruijnEnvShort env 
    | length env <= 2 = "[" ++ intercalate ", " (map shortEntry (reverse env)) ++ "]"
    | otherwise = "[" ++ intercalate ", " (map shortEntry (take 2 (reverse env))) ++ ", ...]"
  where
    shortEntry (CoreFE.ExpE (CoreFE.Rec l _)) = l
    shortEntry (CoreFE.ExpE _) = "_"
    shortEntry (CoreFE.TypE _) = "type"

needsParenCore :: CoreFE.Exp -> Bool
needsParenCore (CoreFE.App _ _) = True
needsParenCore (CoreFE.TApp _ _) = True
needsParenCore (CoreFE.Lam _) = True
needsParenCore (CoreFE.TLam _) = True
needsParenCore _ = False

prettyDeBruijnExp :: CoreFE.Exp -> String
prettyDeBruijnExp (CoreFE.Lit l) = prettyLiteral l
prettyDeBruijnExp (CoreFE.Var n) = "x" ++ show n
prettyDeBruijnExp (CoreFE.Lam e) = "λ. " ++ prettyDeBruijnExp e
prettyDeBruijnExp (CoreFE.TLam e) = "Λ. " ++ prettyDeBruijnExp e
prettyDeBruijnExp (CoreFE.Clos env e) = "⟨[" ++ prettyDeBruijnEnv env ++ "] | " ++ prettyDeBruijnExp e ++ "⟩"
prettyDeBruijnExp (CoreFE.TClos env e) = "⟨[" ++ prettyDeBruijnEnv env ++ "] | " ++ prettyDeBruijnExp e ++ "⟩"
prettyDeBruijnExp (CoreFE.App e1 e2) = prettyDeBruijnExp e1 ++ " " ++ parenIf (needsParenCore e2) (prettyDeBruijnExp e2)
prettyDeBruijnExp (CoreFE.TApp e t) = prettyDeBruijnExp e ++ " @" ++ prettyDeBruijnTyp t
prettyDeBruijnExp (CoreFE.Box env e) = "[" ++ prettyDeBruijnEnv env ++ "] => " ++ prettyDeBruijnExp e
prettyDeBruijnExp (CoreFE.Rec l e) = "{" ++ l ++ " = " ++ prettyDeBruijnExp e ++ "}"
prettyDeBruijnExp (CoreFE.RProj e l) = parenIf (needsParenCore e) (prettyDeBruijnExp e) ++ "." ++ l
prettyDeBruijnExp (CoreFE.FEnv env) = "[" ++ prettyDeBruijnEnv env ++ "]"
prettyDeBruijnExp (CoreFE.Anno e t) = parenIf (needsParenCore e) (prettyDeBruijnExp e) ++ " : " ++ prettyDeBruijnTyp t
prettyDeBruijnExp (CoreFE.Fix e) = "fix " ++ prettyDeBruijnExp e
prettyDeBruijnExp (CoreFE.If e1 e2 e3) = "if " ++ prettyDeBruijnExp e1 ++ " then " ++ prettyDeBruijnExp e2 ++ " else " ++ prettyDeBruijnExp e3
prettyDeBruijnExp (CoreFE.BinOp op) = prettyDeBruijnBinOp op

prettyDeBruijnBinOp :: CoreFE.BinOp -> String
prettyDeBruijnBinOp (CoreFE.Add e1 e2) = prettyDeBruijnExp e1 ++ " + " ++ prettyDeBruijnExp e2
prettyDeBruijnBinOp (CoreFE.Sub e1 e2) = prettyDeBruijnExp e1 ++ " - " ++ prettyDeBruijnExp e2
prettyDeBruijnBinOp (CoreFE.Mul e1 e2) = prettyDeBruijnExp e1 ++ " * " ++ prettyDeBruijnExp e2
prettyDeBruijnBinOp (CoreFE.EqEq e1 e2) = prettyDeBruijnExp e1 ++ " == " ++ prettyDeBruijnExp e2

prettyDeBruijnEnv :: CoreFE.Env -> String
prettyDeBruijnEnv [] = ""
prettyDeBruijnEnv es = intercalate ", " $ map prettyDeBruijnEnvE (reverse es)

prettyDeBruijnEnvE :: CoreFE.EnvE -> String
prettyDeBruijnEnvE (CoreFE.ExpE (CoreFE.Rec l e)) = l ++ " = " ++ prettyDeBruijnExp e
prettyDeBruijnEnvE (CoreFE.ExpE e) = prettyDeBruijnExp e
prettyDeBruijnEnvE (CoreFE.TypE t) = "type " ++ prettyDeBruijnTyp t

prettyDeBruijnTyp :: CoreFE.Typ -> String
prettyDeBruijnTyp (CoreFE.TyLit l) = prettyTyLit l
prettyDeBruijnTyp (CoreFE.TyVar n) = "t" ++ show n
prettyDeBruijnTyp (CoreFE.TyArr t1 t2) =
    let s1 = parenIf (isArrowCore t1) (prettyDeBruijnTyp t1)
        s2 = prettyDeBruijnTyp t2
    in s1 ++ " -> " ++ s2
prettyDeBruijnTyp (CoreFE.TyAll t) = "forall. " ++ prettyDeBruijnTyp t
prettyDeBruijnTyp (CoreFE.TyBoxT env t) = "[" ++ prettyDeBruijnTyEnv env ++ "] => " ++ prettyDeBruijnTyp t
prettyDeBruijnTyp (CoreFE.TySubstT t1 t2) = "#[" ++ prettyDeBruijnTyp t1 ++ "] " ++ prettyDeBruijnTyp t2
prettyDeBruijnTyp (CoreFE.TyRcd l t) = "{" ++ l ++ " : " ++ prettyDeBruijnTyp t ++ "}"
prettyDeBruijnTyp (CoreFE.TyEnvt env) = "Env[" ++ prettyDeBruijnTyEnv env ++ "]"

prettyDeBruijnTyEnv :: CoreFE.TyEnv -> String
prettyDeBruijnTyEnv [] = ""
prettyDeBruijnTyEnv es = intercalate ", " $ map prettyDeBruijnTyEnvE (reverse es)

prettyDeBruijnTyEnvE :: CoreFE.TyEnvE -> String
prettyDeBruijnTyEnvE (CoreFE.Type t) = prettyDeBruijnTyp t
prettyDeBruijnTyEnvE CoreFE.Kind = "*"
prettyDeBruijnTyEnvE (CoreFE.TypeEq t) = "= " ++ prettyDeBruijnTyp t

isArrowCore :: CoreFE.Typ -> Bool
isArrowCore (CoreFE.TyArr _ _) = True
isArrowCore _ = False

prettyCheckResult :: CoreFE.Typ -> String
prettyCheckResult (CoreFE.TyEnvt env) = 
    unlines $ map prettyTypeBinding (reverse env)
  where
    prettyTypeBinding :: CoreFE.TyEnvE -> String
    prettyTypeBinding (CoreFE.Type t) = formatTypeEntry t
    prettyTypeBinding CoreFE.Kind = "  * (kind)"
    prettyTypeBinding (CoreFE.TypeEq t) = "  type = " ++ prettyDeBruijnTyp t
    
    formatTypeEntry :: CoreFE.Typ -> String
    formatTypeEntry (CoreFE.TyRcd label t) = "  " ++ label ++ " : " ++ prettyDeBruijnTyp t
    formatTypeEntry t = "  " ++ prettyDeBruijnTyp t
prettyCheckResult t = "  " ++ prettyDeBruijnTyp t

prettyEvalResult :: CoreFE.Exp -> String
prettyEvalResult (CoreFE.FEnv env) = 
    unlines $ map formatBinding (reverse env)
  where
    formatBinding :: CoreFE.EnvE -> String
    formatBinding (CoreFE.TypE t) = "  type " ++ prettyDeBruijnTyp t
    formatBinding (CoreFE.ExpE e) = formatExpBinding e
    
    formatExpBinding :: CoreFE.Exp -> String
    formatExpBinding (CoreFE.Rec label val) = 
        "  " ++ label ++ " = " ++ prettyValueShort val
    formatExpBinding (CoreFE.Anno (CoreFE.Rec label val) _) = 
        "  " ++ label ++ " = " ++ prettyValueShort val
    formatExpBinding (CoreFE.Anno e _) = 
        "  " ++ prettyValueShort e
    formatExpBinding e = "  " ++ prettyValueShort e
prettyEvalResult e = "  " ++ prettyValueShort e

prettyValueShort :: CoreFE.Exp -> String
prettyValueShort (CoreFE.Lit l) = prettyLiteral l
prettyValueShort (CoreFE.Var n) = "x" ++ show n
prettyValueShort (CoreFE.Clos _ _) = "<closure>"
prettyValueShort (CoreFE.TClos _ _) = "<type-closure>"
prettyValueShort (CoreFE.FEnv env) = prettyDeBruijnEnvShort env
prettyValueShort (CoreFE.Rec label e) = "{" ++ label ++ " = " ++ prettyValueShort e ++ "}"
prettyValueShort (CoreFE.RProj e l) = prettyValueShort e ++ "." ++ l
prettyValueShort (CoreFE.Anno e _) = prettyValueShort e
prettyValueShort e = prettyDeBruijnExpShort e

prettyLiteral :: CoreFE.Literal -> String
prettyLiteral (CoreFE.LitInt n) = show n
prettyLiteral (CoreFE.LitBool b) = if b then "true" else "false"
prettyLiteral (CoreFE.LitStr s) = "\"" ++ s ++ "\""

prettyTyLit :: CoreFE.TyLit -> String
prettyTyLit CoreFE.TyInt  = "int"
prettyTyLit CoreFE.TyBool = "bool"
prettyTyLit CoreFE.TyStr  = "string"