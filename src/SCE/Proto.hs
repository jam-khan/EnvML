module SCE.Proto where

main :: IO ()
main = print "Hello World"


{-

- [ ] LambdaE AST
- [X] LambdaE Type-checking 
- [ ] Small Step Semantics
- [ ] Big Step Semantics

- LambdaSCE AST
- LambdaSCE elaboration to LambdaE
- PBT
- LambdaSCE semantics
- PBT
-}

-- Note: Context is a Type and Environment is an Expression
type Ctx      = Typ 
type Env      = Exp
type Name     = String
type Result a = Either String a

data Typ
  = Int
  | Unit
  | TyAnd Typ Typ
  | TyArr Typ Typ
  | TyRcd Name Typ
  deriving (Eq, Show)

data Exp
  = Query
  | Proj Exp Int
  | Lit  Int
  | UnitE
  | Lam Typ Exp
  | Box Exp Exp
  | Clos Exp Typ Exp
  | App Exp Exp
  | Mrg Exp Exp
  | Rec Name Exp
  | RProj Exp Name
  deriving (Eq, Show)

isValue :: Exp -> Bool
isValue e =
  case e of
    Lit _       -> True
    UnitE       -> True
    Clos e1 _ _ -> isValue e1
    Mrg e1 e2   -> isValue e1 && isValue e2
    Rec _ e'    -> isValue e'
    _ -> False

lookupIdx :: Typ -> Int -> Result Typ
lookupIdx (TyAnd _ b) 0 = pure b
lookupIdx (TyAnd a _) n = lookupIdx a (n - 1)
lookupIdx _ _           = Left "index out of bounds in context"

-- containment judgment: l : A ∈ B
containment :: Name -> Typ -> Result Typ
containment l (TyRcd l' a)
  | l == l'   = pure a
  | otherwise = Left $ "label " ++ l ++ " not found"
containment l (TyAnd b c) =
  case (containment l b, containment l c) of
    (Right a, Left _)  -> pure a   -- ctm-andl
    (Left _,  Right a) -> pure a   -- ctm-andr
    (Right _, Right _) -> Left $ "ambiguous label " ++ l  -- determinism failure
    (Left _,  Left _)  -> Left $ "label " ++ l ++ " not found"
containment l _ = Left $ "label " ++ l ++ " not found"

infer :: Ctx -> Exp -> Result Typ
infer g e =
  case e of
    Query           -> pure g
    Proj e' i       -> do
      ty <- infer g e'
      lookupIdx ty i
    Lit  _          -> pure Int
    UnitE           -> pure Unit
    Lam tyA e'      -> do
      tyB <- infer (TyAnd g tyA) e'
      pure $ TyArr tyA tyB
    Box e1 e2       -> do
      g' <- infer g e1
      infer g' e2
    Clos e1 tyA e2  -> do
      g' <- infer Unit e1
      infer (TyAnd g' tyA) e2
    App e1 e2       -> do
      ty1 <- infer g e1
      ty2 <- infer g e2
      case ty1 of
        TyArr tyA tyB ->
          if tyA == ty2
            then pure tyB
            else Left "types don't match argument and lambda input"
        _ -> Left "App (e1, e2) must have e1 to be function (type A -> B)"
    Mrg e1 e2       -> do
      ty1 <- infer g e1
      ty2 <- infer (TyAnd g ty1) e2
      pure $ TyAnd ty1 ty2
    Rec l e'        -> do
      ty <- infer g e'
      pure $ TyRcd l ty
    RProj e' l      -> do
      ty <- infer g e'
      containment l ty

-- lookupv for runtime values (de Bruijn)
lookupV :: Exp -> Int -> Result Exp
lookupV (Mrg _ v2) 0 = pure v2
lookupV (Mrg v1 _) n = lookupV v1 (n - 1)
lookupV _ _          = Left "lookupV: index out of bounds"

-- selection judgment: v.l ⇝ v'
sel :: Exp -> Name -> Result Exp
sel (Rec l v) l'
  | l == l'   = pure v
  | otherwise = Left $ "sel: label " ++ l' ++ " not found"
sel (Mrg v1 v2) l =
  case (sel v1 l, sel v2 l) of
    (Right v, Left _)  -> pure v
    (Left _,  Right v) -> pure v
    (Right _, Right _) -> Left $ "sel: ambiguous label " ++ l
    (Left _,  Left _)  -> Left $ "sel: label " ++ l ++ " not found"
sel _ l = Left $ "sel: label " ++ l ++ " not found"

-- SMALL-STEP SEMANTICS: env ⊢ e ↦ e'
step :: Env -> Exp -> Result Exp
step env e =
  case e of
    Query -> pure env
    Proj v1 n | isValue v1 ->
      lookupV v1 n
    Proj e1 n ->
      Proj <$> step env e1 <*> pure n
    RProj v1 l | isValue v1 ->
      sel v1 l
    RProj e1 l ->
      RProj <$> step env e1 <*> pure l
    Box v1 v2 | isValue v1, isValue v2 ->
      pure v2
    Box v1 e2 | isValue v1 ->
      Box v1 <$> step v1 e2
    Box e1 e2 ->
      Box <$> step env e1 <*> pure e2
    Lam tyA body ->
      pure $ Clos env tyA body
    App (Clos v1 _ body) v2 | isValue v2 ->
      pure $ Box (Mrg v1 v2) body
    App v1 e2 | isValue v1 ->
      App v1 <$> step env e2
    App e1 e2 ->
      App <$> step env e1 <*> pure e2
    Mrg v1 e2 | isValue v1 ->
      Mrg v1 <$> step (Mrg env v1) e2
    Mrg e1 e2 ->
      Mrg <$> step env e1 <*> pure e2
    Rec l e1 | isValue e1 ->
      pure $ Rec l e1
    Rec l e1 ->
      Rec l <$> step env e1
    _ -> Left $ "stuck: " ++ show e

stepAll :: Exp -> Result Exp
stepAll = go UnitE
  where
    go env e
      | isValue e = pure e
      | otherwise = step env e >>= go env

-- BIG-STEP Semantics: v |- e => e'
bigStep :: Env -> Exp -> Result Exp
bigStep env e =
  case e of
    Query ->
      pure env
    Lit i ->
      pure $ Lit i
    UnitE ->
      pure UnitE
    Clos v1 tyA body | isValue v1 ->
      pure $ Clos v1 tyA body
    Lam tyA body ->
      pure $ Clos env tyA body
    Proj e1 n -> do
      v1 <- bigStep env e1
      lookupV v1 n
    Mrg e1 e2 -> do
      v1 <- bigStep env e1
      v2 <- bigStep (Mrg env v1) e2
      pure $ Mrg v1 v2
    Box e1 e2 -> do
      v1 <- bigStep env e1
      bigStep v1 e2
    App e1 e2 -> do
      clos <- bigStep env e1
      v2 <- bigStep env e2
      case clos of
        Clos v1 _ body -> bigStep (Mrg v1 v2) body
        _ -> Left "app: e1 did not reduce to closure"
    Rec l e1 -> do
      v1 <- bigStep env e1
      pure $ Rec l v1
    RProj e1 l -> do
      v1 <- bigStep env e1
      sel v1 l
    _ -> Left $ "bigStep: stuck on " ++ show e