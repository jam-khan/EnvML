{-# LANGUAGE LambdaCase #-}
module EnvML.DeBruijn where

import qualified EnvML.Parser.AST as S  -- Source (Named, Desugared)
import qualified EnvML.Syntax as T      -- Target (Nameless, Core EnvML)

data CtxEntry = TermEntry S.Name | TypeEntry S.Name
  deriving (Show, Eq)

type Ctx = [CtxEntry]

toDeBruijn :: S.Exp -> T.Exp
toDeBruijn = convExp []

typToDeBruijn :: S.Typ -> T.Typ
typToDeBruijn = convTyp []

modToDeBruijn :: S.Module -> T.Module
modToDeBruijn = convModule []

-- Lookup term variable (skips TypeEntry, counts TermEntry)
lookupVar :: S.Name -> Ctx -> Int
lookupVar x ctx = go ctx 0
  where
    go [] _ = error $ "Unbound variable: " ++ x
    go (TermEntry n : ns) i
      | n == x    = i
      | otherwise = go ns (i + 1)
    go (TypeEntry _ : ns) i = go ns i  -- skip type entries

-- Lookup type variable (skips TermEntry, counts TypeEntry)
lookupTyVar :: S.Name -> Ctx -> Int
lookupTyVar x ctx = go ctx 0
  where
    go [] _ = error $ "Unbound type variable: " ++ x
    go (TypeEntry n : ns) i
      | n == x    = i
      | otherwise = go ns (i + 1)
    go (TermEntry _ : ns) i = go ns i

-- Expression Conversion
convExp :: Ctx -> S.Exp -> T.Exp
convExp ctx = \case
  S.Lit l -> T.Lit (convLit l)
  S.Var x -> T.Var (lookupVar x ctx)
  S.Lam [(x, _arg)] body ->
    T.Lam (convExp (TermEntry x : ctx) body)
  S.Lam _ _ -> 
    error "Multi-arg lambda should be desugared already!"
  S.TLam [(x, S.TyArg)] body ->
    T.TLam (convExp (TypeEntry x : ctx) body)
  S.TLam _ _ ->
    error "Multi-arg TLam should be desugared already!"  
  S.App e1 e2 ->
    T.App (convExp ctx e1) (convExp ctx e2)
  S.TApp e1 t ->
    T.TApp (convExp ctx e1) (convTyp ctx t)
  -- env extends context for body
  S.Clos env [] body ->
    let env' = convEnv ctx env
        envCtx = extractEnvNames env
    in T.Clos env' (convExp envCtx body)
  S.Clos {} ->
    error "Clos should have empty args after desugaring!"
  S.TClos env [] body ->
    let env' = convEnv ctx env
        envCtx = extractEnvNames env
    in T.TClos env' (convExp envCtx body)
  S.TClos {} ->
    error "TClos should have empty args after desugaring!"
  S.Box env e ->
    let env' = convEnv ctx env
        envCtx = extractEnvNames env
    in T.Box env' (convExp envCtx e) 
  S.Rec fields ->
    T.Rec (map (\(n, e) -> (n, convExp ctx e)) fields)
  S.RProj e l ->
    T.RProj (convExp ctx e) l
  S.FEnv env ->
    T.FEnv (convEnv ctx env)
  S.Anno e t ->
    T.Anno (convExp ctx e) (convTyp ctx t)
  S.Mod m ->
    T.ModE (convModule ctx m)
  S.BinOp op ->
    T.BinOp (convBinOp ctx op)

convBinOp :: Ctx -> S.BinOp -> T.BinOp
convBinOp ctx = \case
  S.Add e1 e2 -> T.Add (convExp ctx e1) (convExp ctx e2)
  S.Sub e1 e2 -> T.Sub (convExp ctx e1) (convExp ctx e2)
  S.Mul e1 e2 -> T.Mul (convExp ctx e1) (convExp ctx e2)

convLit :: S.Literal -> T.Literal
convLit = \case
  S.LitInt i -> T.LitInt i
  S.LitBool b -> T.LitBool b
  S.LitStr s -> T.LitStr s

convTyp :: Ctx -> S.Typ -> T.Typ
convTyp ctx = \case
  S.TyLit l -> T.TyLit (convTyLit l)
  S.TyVar x -> T.TyVar (lookupTyVar x ctx)
  S.TyArr t1 t2 ->
    T.TyArr (convTyp ctx t1) (convTyp ctx t2)
  S.TyAll x t ->
    T.TyAll (convTyp (TypeEntry x : ctx) t)
  -- Must reverse environment!
  S.TyBoxT tyCtx t ->
    let tyEnv = convTyCtx ctx tyCtx
        tyCtxNames = extractTyCtxNames tyCtx
    in T.TyBoxT tyEnv (convTyp tyCtxNames t)  
  S.TyRcd fields ->
    T.TyRcd (map (\(n, t) -> (n, convTyp ctx t)) fields)
  S.TyCtx tyCtx ->
    T.TyEnvt (convTyCtx ctx tyCtx)
  S.TyModule mt ->
    T.TyModule (convModuleTyp ctx mt)

convTyLit :: S.TyLit -> T.TyLit
convTyLit = \case
  S.TyInt -> T.TyInt
  S.TyBool -> T.TyBool
  S.TyStr -> T.TyStr

convTyCtx :: Ctx -> S.TyCtx -> T.TyEnv
convTyCtx outerCtx tyCtx =
  let tyCtxNames = extractTyCtxNamesForward tyCtx
      convertAt i e =
        let namesUpTo = reverse (take (i + 1) tyCtxNames)
            ctx = namesUpTo ++ outerCtx
        in convTyCtxE ctx e
      converted = zipWith convertAt [0..] tyCtx
  in reverse converted

extractTyCtxNamesForward :: S.TyCtx -> Ctx
extractTyCtxNamesForward = concatMap getName
  where
    getName (S.TypeN n _) = [TypeEntry n]   -- type annotation
    getName (S.Type _) = []
    getName (S.KindN n) = [TypeEntry n]     -- kind (abstract type)
    getName S.Kind = []
    getName (S.TypeEqN n _) = [TypeEntry n] -- type equation
    getName (S.TyMod n _) = [TermEntry n]   -- module is a term
    getName (S.TypeEqM n _) = [TypeEntry n] -- module type is a type

convTyCtxE :: Ctx -> S.TyCtxE -> T.TyEnvE
convTyCtxE ctx = \case
  S.TypeN _n t      -> T.Type (convTyp ctx t)
  S.Type t          -> T.Type (convTyp ctx t)  
  S.KindN _n        -> T.Kind
  S.Kind            -> T.Kind
  S.TypeEqN _n t    -> T.TypeEq (convTyp ctx t)
  S.TyMod _n mt     -> T.Type (T.TyModule (convModuleTyp ctx mt))  
  S.TypeEqM _n mt   -> T.TypeEq (T.TyModule (convModuleTyp ctx mt))

extractTyCtxNames :: S.TyCtx -> Ctx
extractTyCtxNames = reverse . extractTyCtxNamesForward

convEnv :: Ctx -> S.Env -> T.Env  
convEnv outerCtx env =
  let envNames = extractEnvNamesForward env
      -- For input position i: include names 0..i (including current)
      convertAt i e =
        let namesUpTo = reverse (take (i + 1) envNames)
            ctx = namesUpTo ++ outerCtx
        in convEnvE ctx e
      converted = zipWith convertAt [0..] env
  in reverse converted

extractEnvNamesForward :: S.Env -> Ctx
extractEnvNamesForward = concatMap getName
  where
    getName (S.ExpEN n _) = [TermEntry n]
    getName (S.ExpE _) = []
    getName (S.TypEN n _) = [TypeEntry n]
    getName (S.TypE _) = []
    getName (S.ModE n _) = [TermEntry n]      -- modules are terms
    getName (S.ModTypE n _) = [TypeEntry n]

convEnvE :: Ctx -> S.EnvE -> T.EnvE
convEnvE ctx = \case
  S.ExpEN _n e    -> T.ExpE (convExp ctx e) 
  S.ExpE e        -> T.ExpE (convExp ctx e)  
  S.TypEN _n t    -> T.TypE (convTyp ctx t)  
  S.TypE t        -> T.TypE (convTyp ctx t)
  S.ModE _n m     -> T.ModExpE (T.ModE (convModule ctx m))  
  S.ModTypE _n mt -> T.ModTypE (convTyp ctx (S.TyModule mt))


-- Extract all names from environment (REVERSED to match conversion)
extractEnvNames :: S.Env -> Ctx
extractEnvNames = reverse . extractEnvNamesForward

convModuleTyp :: Ctx -> S.ModuleTyp -> T.ModuleTyp
convModuleTyp ctx = \case
  S.TyArrowM t mt ->
    T.TyArrowM (convTyp ctx t) (convModuleTyp ctx mt)  
  S.ForallM x mt ->
    convModuleTyp (TypeEntry x : ctx) mt
  S.TySig intf ->
    T.TySig (convIntf ctx intf)

convIntf :: Ctx -> S.Intf -> T.Intf
convIntf outerCtx intf =
  let intfNames = extractIntfNamesForward intf
      convertAt i e =
        let namesUpTo = reverse (take (i + 1) intfNames)
            ctx = namesUpTo ++ outerCtx
        in convIntfE ctx e
      converted = zipWith convertAt [0..] intf
  in reverse converted

extractIntfNamesForward :: S.Intf -> Ctx
extractIntfNamesForward = concatMap getName
  where
    getName (S.TyDef n _) = [TypeEntry n]       -- type definition
    getName (S.ValDecl n _) = [TermEntry n]     -- value declaration
    getName (S.ModDecl n _) = [TermEntry n]     -- module is a term
    getName (S.FunctorDecl n _ _) = [TermEntry n]
    getName (S.SigDecl n _) = [TypeEntry n]     -- signature is a type

convIntfE :: Ctx -> S.IntfE -> T.IntfE
convIntfE ctx = \case
  S.TyDef _n t -> T.TyDef (convTyp ctx t)  
  S.ValDecl _n t -> T.ValDecl (convTyp ctx t)
  S.ModDecl _n mt -> T.ModDecl (convTyp ctx (S.TyModule mt))  
  S.FunctorDecl _n _args _mt -> 
    error "FunctorDecl should be desugared to ModDecl!"  
  S.SigDecl _n intf -> T.SigDecl (convTyp ctx (S.TyModule (S.TySig intf)))

-- Module Conversion
convModule :: Ctx -> S.Module -> T.Module
convModule ctx = \case
  S.VarM x -> T.VarM (lookupVar x ctx)
  S.Functor [(x, S.TyArg)] body ->
    T.Functort (convModule (TypeEntry x : ctx) body)  
  S.Functor [(x, _)] body ->
    T.Functor (convModule (TermEntry x : ctx) body)
  S.Functor _ _ ->
    error "Multi-arg functor should be desugared!"
  S.Struct _imports env ->
    let env' = convEnv ctx env
    in T.Struct env'  
  S.MApp m1 m2 ->
    T.MApp (convModule ctx m1) (convModule ctx m2)
  S.MAppt m t ->
    T.MAppt (convModule ctx m) (convTyp ctx t)
  S.MLink _m1 _m2 ->
    error "MLink not supported in core EnvML yet"