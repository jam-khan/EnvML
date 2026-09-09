-- | Name resolution: from the named intermediate ('CoreFE.Named') to the nameless
--   core ('CoreFE.Syntax'). Term and type variables are resolved to separate de
--   Bruijn indices; a literal environment's entries telescope (each entry sees the
--   entries after it) and become a @Unit@-rooted @Merge@ / @TMerge@ chain.
module CoreFE.DeBruijn where

import qualified CoreFE.Syntax    as Nameless
import qualified CoreFE.Named     as Named

type Name       = String
data BindingKind= TermBinding | ModBinding
    deriving (Eq, Show)
type ExpNames   = [(Name, BindingKind)]
type TypNames   = [Name]

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
    -- A module binding is stored as a labelled entry {m = e}; the variable
    -- projects it back out of a singleton environment (Typ-sel with Lookup-rcd).
    (Named.Var n)    ->
      let (i, b) = indexE n eNames
      in  case b of
            TermBinding -> Nameless.Var i
            ModBinding  -> Nameless.RProj (Nameless.Merge Nameless.Unit (Nameless.Var i)) n
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
      toNamelessEnv eNames tNames env
    (Named.Anno e1 ty)   ->
      Nameless.Anno
        (toNamelessExp eNames tNames e1)
        (toNamelessTyp eNames tNames ty)
    (Named.EList es)     ->
      Nameless.EList (map (toNamelessExp eNames tNames) es)
    (Named.ETake i e1)    ->
      Nameless.ETake i (toNamelessExp eNames tNames e1)
    (Named.ELength e1)    ->
      Nameless.ELength (toNamelessExp eNames tNames e1)
    (Named.BinOp op)      ->
      Nameless.BinOp (toNamelessBinOp eNames tNames op)

toNamelessBinOp ::
  ExpNames
  -> TypNames
  -> Named.BinOp
  -> Nameless.BinOp
toNamelessBinOp eNames tNames op =
  let conv = toNamelessExp eNames tNames
  in case op of
       Named.Add      a b -> Nameless.Add      (conv a) (conv b)
       Named.Sub      a b -> Nameless.Sub      (conv a) (conv b)
       Named.Mul      a b -> Nameless.Mul      (conv a) (conv b)
       Named.EqEq     a b -> Nameless.EqEq     (conv a) (conv b)
       Named.LessThan a b -> Nameless.LessThan (conv a) (conv b)

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

-- | A literal environment (newest entry first) becomes a @Unit@-rooted chain.
--   Each entry is resolved in the scope of the entries after it plus the outer
--   scope; a module entry becomes a labelled record entry.
toNamelessEnv ::
  ExpNames
  -> TypNames
  -> Named.Env
  -> Nameless.Exp
toNamelessEnv _ _ [] = Nameless.Unit
toNamelessEnv eNames tNames (e:env) =
  let restExpNames = envToExpNames env ++ eNames
      restTypNames = envToTypNames env ++ tNames
      env' = toNamelessEnv eNames tNames env
  in  case e of
        Named.ExpE _ x -> Nameless.Merge env' (toNamelessExp restExpNames restTypNames x)
        Named.ModE n x -> Nameless.Merge env' (Nameless.Rec n (toNamelessExp restExpNames restTypNames x))
        Named.TypE _ t -> Nameless.TMerge env' (toNamelessTyp restExpNames restTypNames t)

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
    Named.TyList a      ->
      Nameless.TyList (toNamelessTyp eNames tNames a)

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
