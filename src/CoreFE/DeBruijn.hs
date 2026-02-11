module CoreFE.DeBruijn where

import qualified CoreFE.Syntax    as Nameless
import qualified CoreFE.Named     as Named

type Name       = String
data BindingKind= TermBinding | ModBinding
    deriving (Eq, Show)
type ExpNames   = [(Name, BindingKind)]
type TypNames   = [Name]

{-
  Separate contexts as lookupv ignores type equalities.
    Γ : list of term Names   -- term variables only (ExpE and ModE bindings)
    Δ : list of type Names   -- type variables only (TypE bindings)
-}

-- index computation
indexE :: Name -> ExpNames -> (Int, BindingKind)
indexE x []    = error ("unbound: " ++ x)
indexE x ((x', kind):g) = 
  if x == x' then (0, kind) else 
    let (y, kind') = indexE x g
    in  (1 + y, kind')

toNamelessExp :: 
  ExpNames
  -> TypNames
  -> Named.Exp
  -> Nameless.Exp
toNamelessExp eNames tNames e =
  case e of
    (Named.Lit i)    -> Nameless.Lit i
    (Named.Var n)    -> 
      let (i, b) = indexE n eNames
      in  case b of
            TermBinding -> Nameless.Var i
            ModBinding  -> Nameless.RProj (Nameless.FEnv [Nameless.ExpE (Nameless.Var i)]) n
    (Named.Lam x e1) -> 
      Nameless.Lam (toNamelessExp ((x, TermBinding):eNames) tNames e1)
    (Named.Clos env e1)  ->
      Nameless.Clos 
        (toNamelessEnv eNames tNames env)
        (toNamelessExp (envToExpNames env) (envToTypNames env) e1)
    (Named.App e1 e2)    ->
      Nameless.App
        (toNamelessExp eNames tNames e1)
        (toNamelessExp eNames tNames e2)
    (Named.TLam n e1)    ->
      Nameless.TLam (toNamelessExp eNames (n:tNames) e1)
    (Named.TClos env e1) ->
      Nameless.TClos 
        (toNamelessEnv eNames tNames env)
        (toNamelessExp (envToExpNames env) (envToTypNames env) e1)
    (Named.TApp e1 a)    ->
      Nameless.TApp
        (toNamelessExp eNames tNames e1)
        (toNamelessTyp eNames tNames a)
    (Named.Box env e1)   ->
      Nameless.Box
        (toNamelessEnv eNames tNames env)
        (toNamelessExp (envToExpNames env) (envToTypNames env) e1)
    (Named.Rec n e1)     ->
      Nameless.Rec n (toNamelessExp eNames tNames e1)
    (Named.RProj e1 l)   ->
      Nameless.RProj (toNamelessExp eNames tNames e1) l
    (Named.FEnv env)     ->
      Nameless.FEnv (toNamelessEnv eNames tNames env)
    (Named.Anno e1 ty)   ->
      Nameless.Anno 
        (toNamelessExp eNames tNames e1)
        (toNamelessTyp eNames tNames ty)

envToExpNames ::
  Named.Env
  -> ExpNames
envToExpNames [] = []
envToExpNames (Named.ExpE n _:rest) = (n, TermBinding):envToExpNames rest
envToExpNames (Named.ModE n _:rest) = (n, ModBinding):envToExpNames rest
envToExpNames (Named.TypE _ _:rest) = envToExpNames rest

envToTypNames ::
  Named.Env
  -> TypNames
envToTypNames []       = []
envToTypNames (Named.TypE n _: rest) 
                       = n:envToTypNames rest
envToTypNames (_:rest) = envToTypNames rest

toNamelessEnv :: 
  ExpNames
  -> TypNames
  -> Named.Env
  -> Nameless.Env
toNamelessEnv _ _ [] = []
toNamelessEnv eNames tNames (e:env)=
  let restExpNames = envToExpNames env ++ eNames
      restTypNames = envToTypNames env ++ tNames
      e'   = toNamelessEnvE restExpNames restTypNames e 
      env' = toNamelessEnv eNames tNames env
  in  e':env'

toNamelessEnvE ::
  ExpNames
  -> TypNames
  -> Named.EnvE
  -> Nameless.EnvE
toNamelessEnvE eNames tNames entry =
  case entry of
    Named.ExpE _n e -> Nameless.ExpE $ toNamelessExp eNames tNames e
    Named.ModE n e  -> Nameless.ExpE (Nameless.Rec n (toNamelessExp eNames tNames e))
    Named.TypE _n t -> Nameless.TypE $ toNamelessTyp eNames tNames t

getEntryName :: Named.EnvE -> Name
getEntryName (Named.ExpE n _e) = n
getEntryName (Named.ModE n _e) = n
getEntryName (Named.TypE n _e) = n

indexT :: Name -> TypNames -> Int
indexT a []     = error ("unbound" ++ a)
indexT a (a':g) =
  if a == a' then 0 else 1 + indexT a g

toNamelessTyp ::
  ExpNames
  -> TypNames
  -> Named.Typ
  -> Nameless.Typ
toNamelessTyp eNames tNames ty =
  case ty of
    Named.TyLit i       -> Nameless.TyLit i
    Named.TyVar n       -> Nameless.TyVar (indexT n tNames)
    Named.TyArr a b     -> 
      Nameless.TyArr (toNamelessTyp eNames tNames a) (toNamelessTyp eNames tNames b)
    Named.TyAll n a     ->
      Nameless.TyAll (toNamelessTyp eNames (n:tNames) a)
    Named.TyBoxT tyEnv a ->
      Nameless.TyBoxT 
        (toNamelessTyEnv eNames tNames tyEnv)
        (toNamelessTyp [] (getTyEntryNames tyEnv) a)
    Named.TySubstT n a b ->
      Nameless.TySubstT
        (toNamelessTyp eNames tNames a)
        (toNamelessTyp eNames (n:tNames) b)
    Named.TyRcd l a     ->
      Nameless.TyRcd l (toNamelessTyp eNames tNames a)
    Named.TyEnvt env    ->
      Nameless.TyEnvt (toNamelessTyEnv eNames tNames env)

getTyEntryNames ::
  Named.TyEnv
  -> TypNames
getTyEntryNames [] = []
getTyEntryNames ((Named.Type _ _):tyenv) = getTyEntryNames tyenv
getTyEntryNames (t:tyenv)                =
  let names' = getTyEntryNames tyenv
      n = getTyEntryName t
  in  n:names'

getTyEntryName ::
  Named.TyEnvE
  -> Name
getTyEntryName (Named.Type n _)   = n
getTyEntryName (Named.Kind n)     = n
getTyEntryName (Named.TypeEq n _) = n

toNamelessTyEnv :: 
  ExpNames
  -> TypNames
  -> Named.TyEnv
  -> Nameless.TyEnv
toNamelessTyEnv _ _ [] = []
toNamelessTyEnv eNames tNames (t : rest) =
  let restTypNames = getTyEntryNames rest ++ tNames   -- names from rest + outer
      t'    = toNamelessTyEnvE eNames restTypNames t  -- t sees rest + outer
      rest' = toNamelessTyEnv eNames tNames rest      -- rest sees outer only
  in  t' : rest'

toNamelessTyEnvE ::
  ExpNames
  -> TypNames
  -> Named.TyEnvE
  -> Nameless.TyEnvE
toNamelessTyEnvE eNames tNames entry =
  case entry of
    Named.Type _n ty   -> Nameless.Type   (toNamelessTyp eNames tNames ty)
    Named.Kind _n      -> Nameless.Kind
    Named.TypeEq _n ty -> Nameless.TypeEq (toNamelessTyp eNames tNames ty)

toDeBruijn :: Named.Exp -> Nameless.Exp
toDeBruijn = toNamelessExp [] []

toDeBruijnTyp :: Named.Typ -> Nameless.Typ
toDeBruijnTyp = toNamelessTyp [] []