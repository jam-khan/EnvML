module EnvML.Parser.ElabAST where

import qualified EnvML.Parser.AST as N -- Named AST
import qualified EnvML.Syntax     as D -- De-bruijn AST

import Data.List (elemIndex)

type Ctx = [N.Name]

lookupVar :: N.Name -> Ctx -> Int
lookupVar x ctx = 
  case elemIndex x ctx of
    Just i  -> i
    Nothing -> error $ "Unbound type variable: " ++ x

getName :: N.IntfE -> N.Name
getName ie = 
  case ie of
    N.TyDef   n _ -> n
    N.ValDecl n _ -> n
    N.ModDecl n _ -> n 
    N.SigDecl n _ -> n
      
elabTyp :: Ctx -> N.Typ -> D.Typ
elabTyp ctx t = case t of
  N.TyLit l        -> D.TyLit (elabLit l)
  N.TyVar n        -> D.TyVar (lookupVar n ctx)
  N.TyArr t1 t2    -> D.TyArr (elabTyp ctx t1) (elabTyp ctx t2)  
  N.TyAll n t1     -> D.TyAll (elabTyp (n : ctx) t1)
  -- TyBoxT: [t1:A, t2:B] t1 -> t2 ~~> TyBoxT [A, B] _1_ -> _0_
  -- We elaborate the environment entries in the current context.
  -- Then we extend the context for T. We reverse the names so the 
  -- last one in the list (t2) is at the head (index 0).
  N.TyBoxT env t1  -> 
    let g = map (\(_, e) -> elabTyEnvE ctx e) env
        gNames = reverse (map fst env) 
    in D.TyBoxT g (elabTyp gNames t1)
  -- TySubstT: [x:=A] b
  N.TySubstT x a b -> 
    D.TySubstT (elabTyp (x : ctx) a) (elabTyp ctx b)
  
  N.TyRcd s t1     -> D.TyRcd s (elabTyp ctx t1)
  N.TyEnvt env     -> D.TyEnvt (map (\(_, e) -> elabTyEnvE ctx e) env)
  N.TyModule mt    -> D.TyModule (elabModuleTyp ctx mt)

elabTyEnvE :: Ctx -> N.TyEnvE -> D.TyEnvE
elabTyEnvE ctx e = case e of
  N.Type t   -> D.Type (elabTyp ctx t)
  N.Kind     -> D.Kind
  N.TypeEq t -> D.TypeEq (elabTyp ctx t)

elabModuleTyp :: Ctx -> N.ModuleTyp -> D.ModuleTyp
elabModuleTyp ctx mt = case mt of
  N.TyArrowM t mt1 -> D.TyArrowM (elabTyp ctx t) (elabModuleTyp ctx mt1)
  N.TySig intf     -> D.TySig (elabIntf ctx intf)

elabIntf :: Ctx -> N.Intf -> D.Intf
elabIntf ctx intf = elabIntf' ctx intf'
  where 
    intf' = reverse intf
    elabIntf' _ []     = []
    elabIntf' ctx' (x:xs) = elabIntfE ctx' x : elabIntf' (getName x : ctx') xs

elabIntfE :: Ctx -> N.IntfE -> D.IntfE
elabIntfE ctx ie = case ie of
    N.TyDef   _ t    -> D.TyDef   (elabTyp ctx t)
    N.ValDecl _ t    -> D.ValDecl (elabTyp ctx t)
    N.ModDecl _ s    -> D.ModDecl (D.TyVar $ lookupVar s ctx)
    N.SigDecl _ mt   -> D.SigDecl (elabModuleTyp ctx mt)

elabLit :: N.TyLit -> D.TyLit
elabLit N.TyInt  = D.TyInt
elabLit N.TyBool = D.TyBool
elabLit N.TyStr  = D.TyStr
