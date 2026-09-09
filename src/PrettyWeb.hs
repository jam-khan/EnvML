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
prettyEnvMLModuleShort (EnvML.MConcat m1 m2) = prettyEnvMLModuleShort m1 ++ " ++ " ++ prettyEnvMLModuleShort m2
prettyEnvMLModuleShort (EnvML.MDepConcat m1 m2) = prettyEnvMLModuleShort m1 ++ " + " ++ prettyEnvMLModuleShort m2

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
prettyNamedModule (Named.Box [] (Named.Anno e _)) = prettyNamedModule e
prettyNamedModule (Named.Box [] e) = prettyNamedModule e
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
prettyNamedExpShort (Named.EList es) = foldr (\e acc -> acc ++ prettyNamedExpShort e ++ ",") "" es
prettyNamedExpShort (Named.ETake i e) = "take(" ++ show i ++ "," ++ prettyNamedExpShort e ++ ")"
prettyNamedExpShort (Named.ELength e) = "length(" ++ prettyNamedExpShort e ++ ")"
prettyNamedExpShort (Named.BinOp (Named.Add e1 e2))      = prettyNamedExpShort e1 ++ " + "  ++ prettyNamedExpShort e2
prettyNamedExpShort (Named.BinOp (Named.Sub e1 e2))      = prettyNamedExpShort e1 ++ " - "  ++ prettyNamedExpShort e2
prettyNamedExpShort (Named.BinOp (Named.Mul e1 e2))      = prettyNamedExpShort e1 ++ " * "  ++ prettyNamedExpShort e2
prettyNamedExpShort (Named.BinOp (Named.EqEq e1 e2))     = prettyNamedExpShort e1 ++ " == " ++ prettyNamedExpShort e2
prettyNamedExpShort (Named.BinOp (Named.LessThan e1 e2)) = prettyNamedExpShort e1 ++ " < "  ++ prettyNamedExpShort e2


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

-- | A top-level program is a sandboxed environment; show its entries one per line.
prettyDeBruijnModule :: CoreFE.Exp -> String
prettyDeBruijnModule (CoreFE.Box CoreFE.Unit (CoreFE.Anno e _)) = prettyDeBruijnModule e
prettyDeBruijnModule (CoreFE.Box CoreFE.Unit e) = prettyDeBruijnModule e
prettyDeBruijnModule e
  | Just entries <- CoreFE.envEntries e =
      unlines $ map prettyDeBruijnBinding (reverse entries)
  | otherwise = prettyDeBruijnExp e

prettyDeBruijnBinding :: CoreFE.Entry -> String
prettyDeBruijnBinding (CoreFE.EntT t) =
    "type " ++ prettyDeBruijnTyp t
prettyDeBruijnBinding (CoreFE.EntE e) = prettyDeBruijnBindingExp e

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
prettyDeBruijnExpShort e@CoreFE.Unit = prettyDeBruijnEnvShort e
prettyDeBruijnExpShort e@(CoreFE.Merge _ _) = prettyDeBruijnEnvShort e
prettyDeBruijnExpShort e@(CoreFE.TMerge _ _) = prettyDeBruijnEnvShort e
prettyDeBruijnExpShort (CoreFE.Anno e _) = prettyDeBruijnExpShort e
prettyDeBruijnExpShort (CoreFE.BinOp op) = prettyDeBruijnBinOpShort op
prettyDeBruijnExpShort (CoreFE.EList es) = foldr (\e acc -> acc ++ prettyDeBruijnExpShort e ++ ",") "" es
prettyDeBruijnExpShort (CoreFE.ETake i e) = "take(" ++ show i ++ "," ++ prettyDeBruijnExpShort e ++ ")"
prettyDeBruijnExpShort (CoreFE.ELength e) = "length(" ++ prettyDeBruijnExpShort e ++ ")"


prettyDeBruijnBinOpShort :: CoreFE.BinOp -> String
prettyDeBruijnBinOpShort (CoreFE.Add e1 e2) = prettyDeBruijnExpShort e1 ++ " + " ++ prettyDeBruijnExpShort e2
prettyDeBruijnBinOpShort (CoreFE.Sub e1 e2) = prettyDeBruijnExpShort e1 ++ " - " ++ prettyDeBruijnExpShort e2
prettyDeBruijnBinOpShort (CoreFE.Mul e1 e2) = prettyDeBruijnExpShort e1 ++ " * " ++ prettyDeBruijnExpShort e2
prettyDeBruijnBinOpShort (CoreFE.EqEq e1 e2) = prettyDeBruijnExpShort e1 ++ " == " ++ prettyDeBruijnExpShort e2
prettyDeBruijnBinOpShort (CoreFE.LessThan e1 e2) = prettyDeBruijnExpShort e1 ++ " < " ++ prettyDeBruijnExpShort e2

-- | An environment chain, abbreviated. Entries are shown oldest first.
prettyDeBruijnEnvShort :: CoreFE.Exp -> String
prettyDeBruijnEnvShort e =
  case CoreFE.envEntries e of
    Just [] -> "[]"
    Just entries
      | length entries <= 2 -> "[" ++ intercalate ", " (map shortEntry (reverse entries)) ++ "]"
      | otherwise -> "[" ++ intercalate ", " (map shortEntry (take 2 (reverse entries))) ++ ", ...]"
    Nothing -> "(... ,, ...)"
  where
    shortEntry (CoreFE.EntE (CoreFE.Rec l _)) = l
    shortEntry (CoreFE.EntE _) = "_"
    shortEntry (CoreFE.EntT _) = "type"

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
prettyDeBruijnExp (CoreFE.Clos env e) = "⟨" ++ prettyDeBruijnEnvLike env ++ " | " ++ prettyDeBruijnExp e ++ "⟩"
prettyDeBruijnExp (CoreFE.TClos env e) = "⟨" ++ prettyDeBruijnEnvLike env ++ " | " ++ prettyDeBruijnExp e ++ "⟩"
prettyDeBruijnExp (CoreFE.App e1 e2) = prettyDeBruijnExp e1 ++ " " ++ parenIf (needsParenCore e2) (prettyDeBruijnExp e2)
prettyDeBruijnExp (CoreFE.TApp e t) = prettyDeBruijnExp e ++ " @" ++ prettyDeBruijnTyp t
prettyDeBruijnExp (CoreFE.Box env e) = prettyDeBruijnEnvLike env ++ " => " ++ prettyDeBruijnExp e
prettyDeBruijnExp (CoreFE.Rec l e) = "{" ++ l ++ " = " ++ prettyDeBruijnExp e ++ "}"
prettyDeBruijnExp (CoreFE.RProj e l) = parenIf (needsParenCore e) (prettyDeBruijnExp e) ++ "." ++ l
prettyDeBruijnExp e@CoreFE.Unit = prettyDeBruijnEnvLike e
prettyDeBruijnExp e@(CoreFE.Merge _ _) = prettyDeBruijnEnvLike e
prettyDeBruijnExp e@(CoreFE.TMerge _ _) = prettyDeBruijnEnvLike e
prettyDeBruijnExp (CoreFE.Anno e t) = parenIf (needsParenCore e) (prettyDeBruijnExp e) ++ " : " ++ prettyDeBruijnTyp t
prettyDeBruijnExp (CoreFE.BinOp op) = prettyDeBruijnBinOp op
prettyDeBruijnExp (CoreFE.EList es) = foldr (\e acc -> acc ++ prettyDeBruijnExpShort e ++ ",") "" es
prettyDeBruijnExp (CoreFE.ETake i e) = "take(" ++ show i ++ "," ++ prettyDeBruijnExpShort e ++ ")"
prettyDeBruijnExp (CoreFE.ELength e) = "length(" ++ prettyDeBruijnExp e ++ ")"


prettyDeBruijnBinOp :: CoreFE.BinOp -> String
prettyDeBruijnBinOp (CoreFE.Add e1 e2) = prettyDeBruijnExp e1 ++ " + " ++ prettyDeBruijnExp e2
prettyDeBruijnBinOp (CoreFE.Sub e1 e2) = prettyDeBruijnExp e1 ++ " - " ++ prettyDeBruijnExp e2
prettyDeBruijnBinOp (CoreFE.Mul e1 e2) = prettyDeBruijnExp e1 ++ " * " ++ prettyDeBruijnExp e2
prettyDeBruijnBinOp (CoreFE.EqEq e1 e2) = prettyDeBruijnExp e1 ++ " == " ++ prettyDeBruijnExp e2
prettyDeBruijnBinOp (CoreFE.LessThan e1 e2) = prettyDeBruijnExp e1 ++ " < " ++ prettyDeBruijnExp e2

-- | An environment: bracketed entries when literal, the calculus' comma otherwise.
prettyDeBruijnEnvLike :: CoreFE.Exp -> String
prettyDeBruijnEnvLike e =
  case CoreFE.envEntries e of
    Just entries -> "[" ++ intercalate ", " (map prettyDeBruijnEnvE (reverse entries)) ++ "]"
    Nothing ->
      case e of
        CoreFE.Merge d x  -> prettyDeBruijnExp d ++ " ,, " ++ prettyDeBruijnExp x
        CoreFE.TMerge d t -> prettyDeBruijnExp d ++ " ,, type " ++ prettyDeBruijnTyp t
        _                 -> prettyDeBruijnExp e

prettyDeBruijnEnvE :: CoreFE.Entry -> String
prettyDeBruijnEnvE (CoreFE.EntE (CoreFE.Rec l e)) = l ++ " = " ++ prettyDeBruijnExp e
prettyDeBruijnEnvE (CoreFE.EntE e) = prettyDeBruijnExp e
prettyDeBruijnEnvE (CoreFE.EntT t) = "type " ++ prettyDeBruijnTyp t

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
prettyDeBruijnTyp (CoreFE.TyList es) = "list " ++ prettyDeBruijnTyp es

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
prettyCheckResult (CoreFE.TyBoxT [] t) = prettyCheckResult t
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
prettyEvalResult e
  | Just entries <- CoreFE.envEntries e =
      unlines $ map formatBinding (reverse entries)
  | otherwise = "  " ++ prettyValueShort e
  where
    formatBinding :: CoreFE.Entry -> String
    formatBinding (CoreFE.EntT t) = "  type " ++ prettyDeBruijnTyp t
    formatBinding (CoreFE.EntE x) = formatExpBinding x

    formatExpBinding :: CoreFE.Exp -> String
    formatExpBinding (CoreFE.Rec label val) =
        "  " ++ label ++ " = " ++ prettyValueShort val
    formatExpBinding (CoreFE.Anno (CoreFE.Rec label val) _) =
        "  " ++ label ++ " = " ++ prettyValueShort val
    formatExpBinding (CoreFE.Anno x _) =
        "  " ++ prettyValueShort x
    formatExpBinding x = "  " ++ prettyValueShort x

prettyValueShort :: CoreFE.Exp -> String
prettyValueShort (CoreFE.Lit l) = prettyLiteral l
prettyValueShort (CoreFE.Var n) = "x" ++ show n
prettyValueShort (CoreFE.Clos _ _) = "<closure>"
prettyValueShort (CoreFE.TClos _ _) = "<type-closure>"
prettyValueShort e@CoreFE.Unit = prettyDeBruijnEnvShort e
prettyValueShort e@(CoreFE.Merge _ _) = prettyDeBruijnEnvShort e
prettyValueShort e@(CoreFE.TMerge _ _) = prettyDeBruijnEnvShort e
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
