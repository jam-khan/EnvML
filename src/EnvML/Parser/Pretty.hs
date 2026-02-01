module EnvML.Parser.Pretty where

import EnvML.Parser.AST

class Pretty a where
  pretty :: a -> String

instance Pretty Typ where
  pretty = prettyTyp

instance Pretty Exp where
  pretty = prettyExp

instance Pretty Module where
  pretty = prettyModule

instance Pretty Literal where
  pretty = prettyLiteral

instance Pretty TyLit where
  pretty = prettyTyLit

instance Pretty TyCtxE where
  pretty = prettyTyCtxE

instance Pretty IntfE where
  pretty = prettyIntfE

instance Pretty ModuleTyp where
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