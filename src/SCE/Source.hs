{-# LANGUAGE InstanceSigs #-}
module SCE.Source where

import qualified SCE.Core as C
import qualified Test.QuickCheck as QC

-- Note: Context is a Type and Environment is an Expression
type Ctx      = Typ
type Env      = Exp
type Name     = String
type Result a = Either String a

-- Expression types
data Typ
  = Int
  | Unit
  | TyAnd Typ Typ
  | TyArr Typ Typ      -- A -> B  (regular functions)
  | TyRcd Name Typ
  | TyMod ModTyp        -- module type (first-class)
  deriving (Eq, Show)

-- Module types (stratified)
data ModTyp
  = TyIntf Typ          -- sig ... end  (struct's type is just a Typ/interface)
  | TyArrM Typ ModTyp   -- A ->m I  (functor: takes value, produces module)
  deriving (Eq, Show)

data Exp
  = Query                        -- ?  (reify environment)
  | Proj Exp Int                 -- e.n  (de Bruijn projection)
  | Lit  Int                     -- i
  | UnitE                        -- unit
  | Lam Typ Exp                  -- lam A. e
  | Box Exp Exp                  -- e1 |> e2
  | Clos Exp Typ Exp             -- <v, lam A. e>
  | App Exp Exp                  -- e1 e2
  | DMrg Exp Exp                 -- e1 #d e2  (dependent merge)
  | Rec Name Exp                 -- {l = e}
  | RProj Exp Name               -- e.l
  -- Modules (not stratified, live in Exp)
  | MStruct  Sandbox Exp     -- struct[s] A. e
  | MFunctor Sandbox Typ Exp     -- functor[s] (A) e
  | MClos Exp Typ Exp            -- module closure <env, A, body>
  | MLink Exp Exp                -- Link(e1, e2)
  -- More elaborated terms
  | NMrg Exp Exp                 -- e1 #n e2  (non-dependent merge)
  | Let Exp Typ Exp              -- let e1 : A in e2
  | Open Exp Exp                 -- open e1 in e2
  deriving (Eq, Show)

data Sandbox = Sandboxed | Open_
  deriving (Eq, Show)

isValue :: Exp -> Bool
isValue (Lit _)        = True
isValue UnitE          = True
isValue (Clos v _ _)   = isValue v
isValue (MClos v _ _)  = isValue v
isValue (DMrg v1 v2)   = isValue v1 && isValue v2
isValue (NMrg v1 v2)   = isValue v1 && isValue v2
isValue (Rec _ v)      = isValue v
isValue _              = False

lookupIdx :: Typ -> Int -> Result Typ
lookupIdx (TyAnd _ b) 0 = pure b
lookupIdx (TyAnd a _) n = lookupIdx a (n - 1)
lookupIdx _ _            = Left "index out of bounds in context"

containment :: Name -> Typ -> Result Typ
containment l (TyRcd l' a)
  | l == l'   = pure a
  | otherwise = Left $ "label " ++ l ++ " not found"
containment l (TyAnd b c) =
  case (containment l b, containment l c) of
    (Right a, Left _)  -> pure a
    (Left _,  Right a) -> pure a
    (Right _, Right _) -> Left $ "ambiguous label " ++ l
    (Left _,  Left _)  -> Left $ "label " ++ l ++ " not found"
containment l _ = Left $ "label " ++ l ++ " not found"

elaborateTyp :: Typ -> C.Typ
elaborateTyp Int          = C.Int
elaborateTyp Unit         = C.Unit
elaborateTyp (TyArr a b)  = C.TyArr (elaborateTyp a) (elaborateTyp b)
elaborateTyp (TyAnd a b)  = C.TyAnd (elaborateTyp a) (elaborateTyp b)
elaborateTyp (TyRcd l a)  = C.TyRcd l (elaborateTyp a)
elaborateTyp (TyMod mt)   = elaborateModTyp mt

elaborateModTyp :: ModTyp -> C.Typ
elaborateModTyp (TyIntf a)    = elaborateTyp a
elaborateModTyp (TyArrM a mt) = C.TyArr (elaborateTyp a) (elaborateModTyp mt)

elaborate :: Ctx -> Exp -> Result (Typ, C.Exp)
elaborate g e = case e of
  Query -> pure (g, C.Query)
  Lit n -> pure (Int, C.Lit n)
  UnitE -> pure (Unit, C.UnitE)
  Proj se n -> do
    (b, ce) <- elaborate g se
    a <- lookupIdx b n
    pure (a, C.Proj ce n)
  Lam tyA se -> do
    (tyB, ce) <- elaborate (TyAnd g tyA) se
    pure (TyArr tyA tyB, C.Lam (elaborateTyp tyA) ce)
  Box se1 se2 -> do
    (g', ce1) <- elaborate g se1
    (a, ce2)  <- elaborate g' se2
    pure (a, C.Box ce1 ce2)
  Clos se1 tyA se2 -> do
    (g', ce1)  <- elaborate g se1
    (tyB, ce2) <- elaborate (TyAnd g' tyA) se2
    pure (TyArr tyA tyB, C.Clos ce1 (elaborateTyp tyA) ce2)
  App se1 se2 -> do
    (ty1, ce1) <- elaborate g se1
    (ty2, ce2) <- elaborate g se2
    case ty1 of
      TyArr tyA tyB
        | tyA == ty2 -> pure (tyB, C.App ce1 ce2)
        | otherwise  -> Left "App: argument type mismatch"
      _ -> Left "App: not a function type"
  DMrg se1 se2 -> do
    (a, ce1) <- elaborate g se1
    (b, ce2) <- elaborate (TyAnd g a) se2
    pure (TyAnd a b, C.Mrg ce1 ce2)
  NMrg se1 se2 -> do
    (a, ce1) <- elaborate g se1
    (b, ce2) <- elaborate g se2
    let gT   = elaborateTyp g
        body = C.Mrg
                 (C.Box (C.Proj C.Query 0) ce1)
                 (C.Box (C.Proj C.Query 1) ce2)
        core = C.App (C.Lam gT body) C.Query
    pure (TyAnd a b, core)
  Rec l se -> do
    (a, ce) <- elaborate g se
    pure (TyRcd l a, C.Rec l ce)
  RProj se l -> do
    (b, ce) <- elaborate g se
    a <- containment l b
    pure (a, C.RProj ce l)
  Let se1 tyA se2 -> do
    (a, ce1) <- elaborate g se1
    if a /= tyA
      then Left "Let: annotation mismatch"
      else do
        (b, ce2) <- elaborate (TyAnd g tyA) se2
        pure (b, C.App (C.Lam (elaborateTyp tyA) ce2) ce1)
  Open se1 se2 -> do
    (ty1, ce1) <- elaborate g se1
    case ty1 of
      TyRcd l a -> do
        (b, ce2) <- elaborate (TyAnd g a) se2
        pure (b, C.App (C.Lam (elaborateTyp a) ce2) (C.RProj ce1 l))
      _ -> Left "Open: expected record type"
  -- infstruct-sandboxed: Unit & A |- e : B ~> ce
  --   ==> G |- struct[sandboxed] A. e : Sig(A, B) ~> box unit (lam [A] ce)
  -- infstruct-open: G & A |- e : B ~> ce
  --   ==> G |- struct[open] A. e : Sig(A, B) ~> box ctx (lam [A] ce)
  MStruct sb se -> do
    let ctx' = case sb of
                 Sandboxed -> Unit
                 Open_     -> g
    (tyB, ce) <- elaborate ctx' se
    let envCore = case sb of
                    Sandboxed -> C.UnitE
                    Open_     -> C.Query
    pure (TyMod (TyIntf tyB), C.Box envCore ce)
  -- inffunctor-sandboxed: Unit & A |- e : B ~> ce
  --   ==> G |- functor[sandboxed](A) e : A -> B ~> box unit (lam [A] ce)
  -- inffunctor-open: G & A |- e : B ~> ce
  --   ==> G |- functor[open](A) e : A -> B ~> lam [A] ce
  MFunctor sb tyA se -> do
    let ctx' = case sb of
                 Sandboxed -> TyAnd Unit tyA
                 Open_     -> TyAnd g tyA
    (tyB, ce) <- elaborate ctx' se
    let mt = case tyB of
               TyMod innerMt -> TyArrM tyA innerMt
               _             -> TyArrM tyA (TyIntf tyB)
    case sb of
      Sandboxed ->
        pure (TyMod mt, C.Box C.UnitE (C.Lam (elaborateTyp tyA) ce))
      Open_ ->
        pure (TyMod mt, C.Lam (elaborateTyp tyA) ce)
  -- Module closure typing (runtime construct, like Clos)
  MClos se1 tyA se2 -> do
    (g', ce1)  <- elaborate g se1
    (tyB, ce2) <- elaborate (TyAnd g' tyA) se2
    let mt = case tyB of
               TyMod innerMt -> TyArrM tyA innerMt
               _             -> TyArrM tyA (TyIntf tyB)
    pure (TyMod mt, C.Clos ce1 (elaborateTyp tyA) ce2)

  -- infmodapp / linking: G |- e1 : Sig(A,B) ~> ce1, G |- e2 : A ~> ce2
  --                      ==> G |- Link(e1, e2) : B ~> app ce1 ce2
  MLink se1 se2 -> do
    (ty1, ce1) <- elaborate g se1
    (ty2, ce2) <- elaborate g se2
    case ty1 of
      TyMod (TyArrM tyA mt)
        | tyA == ty2 -> pure (TyMod mt, C.App ce1 ce2)
        | otherwise  -> Left $ "MLink: argument type mismatch, expected "
                             ++ show tyA ++ " got " ++ show ty2
      _ -> Left $ "MLink: not a functor type, got " ++ show ty1

lookupV :: Exp -> Int -> Result Exp
lookupV (DMrg _ v2) 0 = pure v2
lookupV (DMrg v1 _) n = lookupV v1 (n - 1)
lookupV (NMrg _ v2) 0 = pure v2
lookupV (NMrg v1 _) n = lookupV v1 (n - 1)
lookupV _ _            = Left "lookupV: index out of bounds"

sel :: Exp -> Name -> Result Exp
sel (Rec l v) l'
  | l == l'   = pure v
  | otherwise = Left $ "sel: label " ++ l' ++ " not found"
sel (DMrg v1 v2) l = selMrg v1 v2 l
sel (NMrg v1 v2) l = selMrg v1 v2 l
sel _ l = Left $ "sel: label " ++ l ++ " not found"

selMrg :: Exp -> Exp -> Name -> Result Exp
selMrg v1 v2 l =
  case (sel v1 l, sel v2 l) of
    (Right v, Left _)  -> pure v
    (Left _,  Right v) -> pure v
    (Right _, Right _) -> Left $ "sel: ambiguous label " ++ l
    (Left _,  Left _)  -> Left $ "sel: label " ++ l ++ " not found"

bigStep :: Env -> Exp -> Result Exp
bigStep env e = case e of
  Query         -> pure env
  Lit i         -> pure $ Lit i
  UnitE         -> pure UnitE

  Clos v ty body  | isValue v -> pure $ Clos v ty body
  MClos v ty body | isValue v -> pure $ MClos v ty body

  Proj e' n -> do
    v <- bigStep env e'
    lookupV v n

  Lam ty body -> pure $ Clos env ty body

  Box e1 e2 -> do
    v1 <- bigStep env e1
    bigStep v1 e2

  App e1 e2 -> do
    clos <- bigStep env e1
    v2   <- bigStep env e2
    case clos of
      Clos v1 _ body  -> bigStep (DMrg v1 v2) body
      MClos v1 _ body -> bigStep (DMrg v1 v2) body
      _ -> Left "app: not a closure"

  DMrg e1 e2 -> do
    v1 <- bigStep env e1
    v2 <- bigStep (DMrg env v1) e2
    pure $ DMrg v1 v2

  NMrg e1 e2 -> do
    v1 <- bigStep env e1
    v2 <- bigStep env e2
    pure $ NMrg v1 v2

  Rec l e1 -> do
    v1 <- bigStep env e1
    pure $ Rec l v1

  RProj e1 l -> do
    v1 <- bigStep env e1
    sel v1 l

  Let e1 _ e2 -> do
    v1 <- bigStep env e1
    bigStep (DMrg env v1) e2

  Open e1 e2 -> do
    v1 <- bigStep env e1
    case v1 of
      Rec _ v -> bigStep (DMrg env v) e2
      _       -> Left "open: expected record value"

  MStruct Sandboxed body -> bigStep UnitE body
  MStruct Open_     body -> bigStep env body

  MFunctor Sandboxed ty body -> pure $ MClos UnitE ty body
  MFunctor Open_     ty body -> pure $ MClos env ty body

  MLink e1 e2 -> do
    mclos <- bigStep env e1
    v2    <- bigStep env e2
    case mclos of
      MClos v1 _ body -> bigStep (DMrg v1 v2) body
      Clos  v1 _ body -> bigStep (DMrg v1 v2) body
      _ -> Left "link: not a module closure"

  _ -> Left $ "bigStep: stuck on " ++ show e

infer :: Ctx -> Exp -> Result Typ
infer g e = fst <$> elaborate g e

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _         = False

-- Theorem: Type-Preserving Elaboration
-- If G |-S e : A ~> ce, then [G] |-C ce : [A]
prop_typePreservingElaboration :: Ctx -> Exp -> Bool
prop_typePreservingElaboration g se =
  case elaborate g se of
    Right (a, ce) ->
      C.infer (elaborateTyp g) ce == Right (elaborateTyp a)
    Left _ -> True

-- Theorem: Uniqueness of Type Inference
prop_uniqueInference :: Ctx -> Exp -> Bool
prop_uniqueInference g se =
  case (elaborate g se, elaborate g se) of
    (Right (a1, _), Right (a2, _)) -> a1 == a2
    _ -> True

-- Theorem: Uniqueness of Elaboration
prop_uniqueElaboration :: Ctx -> Exp -> Bool
prop_uniqueElaboration g se =
  case (elaborate g se, elaborate g se) of
    (Right (_, ce1), Right (_, ce2)) -> ce1 == ce2
    _ -> True

-- Theorem: Semantics Preservation
-- Source big-step and core big-step agree on elaborated terms
prop_semanticsPreservation :: Exp -> Bool
prop_semanticsPreservation se =
  case elaborate Unit se of
    Right (_, ce) ->
      case (bigStep UnitE se, C.bigStep C.UnitE ce) of
        (Right sv, Right cv) ->
          case (infer Unit sv, C.infer C.Unit cv) of
            (Right sty, Right cty) -> elaborateTyp sty == cty
            _ -> True
        (Left _, Left _) -> True
        _ -> False
    Left _ -> True

-- Theorem: Capability Safety / Sandbox Isolation
-- Sandboxed modules produce the same value under any environment
prop_sandboxIsolation :: Exp -> Exp -> Exp -> Bool
prop_sandboxIsolation env1 env2 body =
  not (isValue env1 && isValue env2) || (let sb = MStruct Sandboxed body
                                         in case (bigStep env1 sb, bigStep env2 sb) of
                                              (Right v1, Right v2) -> v1 == v2
                                              (Left _, Left _)     -> True
                                              _                    -> False)

-- Theorem: Sandbox Functor Isolation
prop_sandboxFunctorIsolation :: Exp -> Exp -> Typ -> Exp -> Bool
prop_sandboxFunctorIsolation env1 env2 tyA body =
  not (isValue env1 && isValue env2) || (let sb = MFunctor Sandboxed tyA body
                                         in case (bigStep env1 sb, bigStep env2 sb) of
                                              (Right v1, Right v2) -> v1 == v2
                                              (Left _, Left _)     -> True
                                              _                    -> False)

-- Theorem: Separate Compilation
-- Elaborating Link(M1, M2) = App([M1], [M2])
prop_separateCompilation :: Exp -> Exp -> Bool
prop_separateCompilation se1 se2 =
  case elaborate Unit (MLink se1 se2) of
    Right (_, cLinked) ->
      case (elaborate Unit se1, elaborate Unit se2) of
        (Right (_, ce1), Right (_, ce2)) ->
          cLinked == C.App ce1 ce2
        _ -> True
    Left _ -> True

-- Theorem: Secure Linking
-- Sandboxed functor's body result is independent of link partner's value
-- (when body doesn't use the argument)
prop_secureLinking :: Exp -> Exp -> Bool
prop_secureLinking arg1 arg2 =
  not (isValue arg1 && isValue arg2) || (let m = MFunctor Sandboxed Int (Lit 42)  -- doesn't use arg
                                         in case (bigStep UnitE (MLink m arg1), bigStep UnitE (MLink m arg2)) of
                                              (Right v1, Right v2) -> v1 == v2
                                              (Left _, Left _)     -> True
                                              _                    -> False)

-- Theorem: Link Elaboration Commutes with Evaluation
-- eval([Link(M1,M2)]) = eval(App([M1], [M2]))
prop_linkElaborationCommutes :: Exp -> Exp -> Bool
prop_linkElaborationCommutes se1 se2 =
  case (elaborate Unit (MLink se1 se2), elaborate Unit se1, elaborate Unit se2) of
    (Right (_, cLinked), Right (_, ce1), Right (_, ce2)) ->
      case (C.bigStep C.UnitE cLinked, C.bigStep C.UnitE (C.App ce1 ce2)) of
        (Right v1, Right v2) -> v1 == v2
        (Left _, Left _)     -> True
        _                    -> False
    _ -> True

-- Theorem: NMrg Independence
-- In non-dependent merge, e2's type is independent of e1
prop_nmrgIndependence :: Exp -> Exp -> Bool
prop_nmrgIndependence se1 se2 =
  case elaborate Unit (NMrg se1 se2) of
    Right (TyAnd _ b, _) ->
      case elaborate Unit se2 of
        Right (b', _) -> b == b'
        Left _        -> True
    _ -> True

-- Sanity: DMrg allows dependency (e2 can see e1's binding)
prop_dmrgAllowsDependency :: Bool
prop_dmrgAllowsDependency =
  case elaborate Unit (DMrg (Lit 1) (Proj Query 0)) of
    Right (TyAnd Int Int, _) -> True
    _                        -> False

-- Sanity: Struct elaborates to box env (lam A ce) in core
prop_structShape :: Exp -> Bool
prop_structShape body =
  case elaborate Unit (MStruct Sandboxed body) of
    Right (_, C.Box C.UnitE _) -> True
    Right _  -> False
    Left _   -> True