module EnvML.Print where

import EnvML.Syntax

main :: IO ()
main = error "TODO"

type Precedence = Int

typPrec :: Typ -> Precedence
typPrec t = case t of
  TyLit _ -> 4
  TyVar _ -> 4
  TyRcd _ _ -> 4
  TyEnvt _ -> 4
  TyModule _ -> 4
  TySubstT {} -> 3
  TyArr _ _ -> 2
  TyBoxT _ _ -> 1
  TyAll _ _ -> 1

expPrec :: Exp -> Precedence
expPrec e = case e of
  Anno _ _ -> 0
  Box _ _ -> 1
  Clos {} -> 1
  TClos {} -> 1
  Lam {}-> 2
  TLam {} -> 2
  App _ _ -> 3
  TApp _ _ -> 3
  RProj _ _ -> 4
  Lit _ -> 5
  Var _ -> 5
  Rec _ _ -> 5
  FEnv _ -> 5
  ModE _ -> 5

parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s

stringOfTyBind :: (Name, TyEnvE) -> String
stringOfTyBind (n, Type t) = n ++ " : " ++ stringOfTyp t
stringOfTyBind (n, Kind) = n ++ " : Type"
stringOfTyBind (n, TypeEq t) = n ++ " = " ++ stringOfTyp t

stringOfTyEnv :: TyEnv -> String
stringOfTyEnv [] = ""
stringOfTyEnv [b] = stringOfTyBind b
stringOfTyEnv (b : bs) = stringOfTyBind b ++ ", " ++ stringOfTyEnv bs

stringOfEnvBind :: (Name, EnvE) -> String
stringOfEnvBind (n, ExpE e) = n ++ " = " ++ stringOfExp e
stringOfEnvBind (n, TypE t) = n ++ " : " ++ stringOfTyp t

stringOfEnv :: Env -> String
stringOfEnv [] = ""
stringOfEnv [b] = stringOfEnvBind b
stringOfEnv (b : bs) = stringOfEnvBind b ++ ", " ++ stringOfEnv bs

rShowBinds :: TyEnv -> String
rShowBinds = stringOfTyEnv . reverse

stringOfIntfE :: IntfE -> String
stringOfIntfE (TyDef n t) = "type " ++ show n ++ " = " ++ stringOfTyp t
stringOfIntfE (ValDecl n t) = "val " ++ show n  ++ " :  "  ++ stringOfTyp t
stringOfIntfE (ModDecl n1 n2) = "module " ++ show n1  ++ " :  "  ++ show n2
stringOfIntfE (SigDecl n mt) = "module type " ++ show n  ++ " = "  ++ stringOfModuleTyp mt

stringOfIntf :: Intf -> String
stringOfIntf [] = ""
stringOfIntf [e] = stringOfIntfE e
stringOfIntf (e:es) = stringOfIntfE e ++ "; " ++ stringOfIntf es

stringOfModuleTyp :: ModuleTyp -> String
stringOfModuleTyp (TyArrowM t m) = 
    let sT = stringOfTyp t
        sM = stringOfModuleTyp m
     in "(" ++ sT ++ " -> " ++ sM ++ ")"
stringOfModuleTyp (TySig mt) = 
    let sIntf = stringOfIntf mt
     in "sig " ++ sIntf ++ " end"

stringOfModule :: Module -> String
stringOfModule (Functor n t m) =
    let sT = stringOfTyp t
        sM = stringOfModule m
     in "functor (" ++ show n ++ " : " ++ sT ++ ") " ++ sM
stringOfModule (Struct env) = 
    let sEnv = stringOfEnv env
     in "struct " ++ sEnv ++ " end"
stringOfModule (MApp m1 m2) = 
    let sM1 = stringOfModule m1
        sM2 = stringOfModule m2
     in "( " ++ sM1 ++ ") ( " ++ sM2 ++ " )"
stringOfModule (MLink m1 m2) = 
    let sM1 = stringOfModule m1
        sM2 = stringOfModule m2
     in "( " ++ sM1 ++ " ) |><| ( " ++ sM2 ++ " )"


stringOfTyp :: Typ -> String
stringOfTyp (TyLit n) = show n
stringOfTyp (TyVar s) = show s
stringOfTyp (TyArr t1 t2) =
  let s1 = parensIf (typPrec t1 <= typPrec (TyArr t1 t2)) (stringOfTyp t1)
      s2 = stringOfTyp t2
   in s1 ++ " -> " ++ s2
stringOfTyp (TyAll x t) =
  let s = parensIf (typPrec t < typPrec (TyAll x t)) (stringOfTyp t)
   in "forall " ++ show x ++ ". " ++ s
stringOfTyp (TyBoxT bs t) =
  let sBinds = rShowBinds bs
      sTyp = parensIf (typPrec t < typPrec (TyBoxT bs t)) (stringOfTyp t)
   in "[" ++ sBinds ++ "] ===> " ++ sTyp
stringOfTyp (TySubstT t1 x t2) =
  let s1 = stringOfTyp t1
      s2 = parensIf (typPrec t2 < typPrec (TySubstT t1 x t2)) (stringOfTyp t2)
   in s1 ++ "[" ++ show x ++ ":=" ++ s2 ++ "]"
stringOfTyp (TyEnvt bs) = "[" ++ rShowBinds bs ++ "]"
stringOfTyp (TyRcd label t) = "{" ++ label ++ " : " ++ stringOfTyp t ++ "}"
stringOfTyp (TyModule mt) = stringOfModuleTyp mt

stringOfExp :: Exp -> String
stringOfExp (Lit n) = show n
stringOfExp (Var n) = show n
stringOfExp (Lam n t e) =
  let sT = stringOfTyp t
      sE = stringOfExp e
   in "fun (" ++ show n ++ " : " ++ sT ++ ") -> " ++ sE
stringOfExp (Box env e) =
  let sCets = stringOfEnv env
      sE = parensIf (expPrec e < expPrec (Box env e)) (stringOfExp e)
   in "box [" ++ sCets ++ "] |> in " ++ sE
stringOfExp (App e1 e2) =
  let s1 = parensIf (expPrec e1 < expPrec (App e1 e2)) (stringOfExp e1)
      s2 = stringOfExp e2
   in s1 ++ " ( " ++ s2 ++ " )"
stringOfExp (TLam n e) =
    let sE = stringOfExp e
     in "fun type " ++ show n ++ " -> " ++ sE
stringOfExp (Clos cetList n t e) =
  let sCets = stringOfEnv cetList
      sT = stringOfTyp t
      sE = parensIf (expPrec e < expPrec (Clos cetList n t e)) (stringOfExp e)
   in "clos [ " ++ sCets ++ " ] (" ++ show n ++ " : " ++ sT ++ ") -> " ++ sE
stringOfExp (TClos cetList n e) =
  let sCets = stringOfEnv cetList
      sE = parensIf (expPrec e < expPrec (TClos cetList n e)) (stringOfExp e)
   in "clos [ " ++ sCets ++ " ] type " ++ show n ++ "-> " ++ sE
stringOfExp (TApp e t) =
  let sE = parensIf (expPrec e < expPrec (TApp e t)) (stringOfExp e)
      sT = stringOfTyp t
   in sE ++ "< " ++ sT ++ " >"
stringOfExp (FEnv env) =
  let sEnv = stringOfEnv env
   in "[" ++ sEnv ++ "]"
stringOfExp (Rec label e) =
  let sE = stringOfExp e
   in "{" ++ label ++ " = " ++ sE ++ "}"
stringOfExp (RProj e label) =
  let sE = parensIf (expPrec e < expPrec (RProj e label)) (stringOfExp e)
   in sE ++ "." ++ label
stringOfExp (Anno e t) =
  let sE = parensIf (expPrec e < expPrec (Anno e t)) (stringOfExp e)
      sT = stringOfTyp t
   in sE ++ " :: " ++ sT
stringOfExp (ModE m) = stringOfModule m

