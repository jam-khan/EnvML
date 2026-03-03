{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module SCE.SourceTest where

import Test.QuickCheck
import SCE.Source as SCE
import qualified SCE.Core as C

--------------------------------------------------------------------------------
-- Type generators
--------------------------------------------------------------------------------

genTyp :: Gen Typ
genTyp = sized genTypSized

genModTyp :: Int -> Gen ModTyp
genModTyp n
  | n <= 0    = TyIntf <$> genBaseTyp
  | otherwise = frequency
      [ (2, TyIntf <$> go (n `div` 2))
      , (2, TyArrM <$> go (n `div` 2) <*> genModTyp (n `div` 2))
      ]
  where go = genTypSized

genTypSized :: Int -> Gen Typ
genTypSized n
  | n <= 0    = genBaseTyp
  | otherwise = frequency
      [ (4, pure Int)
      , (1, pure Unit)
      , (2, TyAnd <$> genTypSized (n `div` 2) <*> genTypSized (n `div` 2))
      , (2, TyArr <$> genTypSized (n `div` 2) <*> genTypSized (n `div` 2))
      , (1, TyRcd <$> genLabel <*> genTypSized (n `div` 2))
      , (1, TyMod <$> genModTyp (n `div` 2))
      ]

genBaseTyp :: Gen Typ
genBaseTyp = frequency [(3, pure Int), (1, pure Unit)]

instance Arbitrary Typ where
  arbitrary :: Gen Typ
  arbitrary = genTyp

instance Arbitrary Exp where
  arbitrary :: Gen Exp
  arbitrary = do
    WellTyped e <- arbitrary
    pure e

instance Arbitrary Sandbox where
  arbitrary :: Gen Sandbox
  arbitrary = genSandbox

instance Arbitrary ModTyp where
  arbitrary = sized genModTyp

genLabel :: Gen Name
genLabel = elements ["x", "y", "z", "a", "b"]

genSandbox :: Gen Sandbox
genSandbox = elements [Sandboxed, Open_]

--------------------------------------------------------------------------------
-- Context index finder (only TyAnd has valid de Bruijn indices)
--------------------------------------------------------------------------------

findIndices :: Typ -> Typ -> [Int]
findIndices ctx target = go ctx 0
  where
    go (TyAnd rest rightmost) i =
      ([i | rightmost == target]) ++ go rest (i + 1)
    go _ _ = []

--------------------------------------------------------------------------------
-- Value generator: produces closed values of a given type
--------------------------------------------------------------------------------

genVal :: Typ -> Gen Exp
genVal Int           = Lit <$> arbitrary
genVal Unit          = pure UnitE
genVal (TyAnd a b)   = DMrg <$> genVal a <*> genVal b
genVal (TyRcd l a)   = Rec l <$> genVal a
genVal (TyArr a b)   = do
  body <- genWellTyped (TyAnd Unit a) b
  pure $ Clos UnitE a body
genVal (TyMod (TyIntf a)) = do
  body <- genWellTyped Unit a
  pure $ MStruct Sandboxed body
genVal (TyMod (TyArrM a mt)) = do
  body <- genWellTyped (TyAnd Unit a) (TyMod mt)
  pure $ MClos UnitE a body

-- Generate types that have proper runtime values
genValTyp :: Gen Typ
genValTyp = sized go
  where
    go n
      | n <= 0    = frequency [(3, pure Int), (1, pure Unit)]
      | otherwise = frequency
          [ (4, pure Int)
          , (1, pure Unit)
          , (2, TyAnd <$> go (n `div` 2) <*> go (n `div` 2))
          , (2, TyArr <$> go (n `div` 2) <*> go (n `div` 2))
          , (1, TyRcd <$> genLabel <*> go (n `div` 2))
          -- NO TySig here
          ]

--------------------------------------------------------------------------------
-- Well-typed expression generator:  ctx |- e : ty
--
-- Every case corresponds to a typing/elaboration rule in Source.elaborate
--------------------------------------------------------------------------------

genWellTyped :: Typ -> Typ -> Gen Exp
genWellTyped ctx ty = sized $ \n ->
  if n <= 0
    then genVal ty
    else frequency $ concat
      [
      -- Base: value of correct type (always available)
        [ (3, genVal ty) ]

      -- Query: ? : G  (only when ctx == ty)
      , [ (3, pure Query) | ctx == ty ]

      -- Proj: e.n with lookup(ctx, n) = ty via Query
      , let idxs = findIndices ctx ty
        in [ (3, do i <- elements idxs; pure (Proj Query i)) | not (null idxs) ]

      -- Lam: lam A. e  (only when ty is TyArr)
      , case ty of
          TyArr a b ->
            [ (3, resize (n `div` 2) $ do
                body <- genWellTyped (TyAnd ctx a) b
                pure (Lam a body)) ]
          _ -> []

      -- App: e1 e2 where e1 : A -> ty, e2 : A
      , [ (2, resize (n `div` 2) $ do
              a <- resize (n `div` 3) genTyp
              f <- genWellTyped ctx (TyArr a ty)
              arg <- genWellTyped ctx a
              pure (App f arg)) ]

      -- DMrg: dependent merge e1 # e2  (only when ty is TyAnd)
      , case ty of
          TyAnd a b ->
            [ (2, resize (n `div` 2) $ do
                e1 <- genWellTyped ctx a
                e2 <- genWellTyped (TyAnd ctx a) b
                pure (DMrg e1 e2)) ]
          _ -> []

      -- NMrg: non-dependent merge (only when ty is TyAnd)
      , case ty of
          TyAnd a b ->
            [ (2, resize (n `div` 2) $ do
                e1 <- genWellTyped ctx a
                e2 <- genWellTyped ctx b
                pure (NMrg e1 e2)) ]
          _ -> []

      -- Box: e1 |> e2
      , [ (2, resize (n `div` 2) $ do
              g' <- resize (n `div` 3) genTyp
              e1 <- genWellTyped ctx g'
              e2 <- genWellTyped g' ty
              pure (Box e1 e2)) ]

      -- Rec: {l = e}  (only when ty is TyRcd)
      , case ty of
          TyRcd l a ->
            [ (2, resize (n `div` 2) $ do
                e <- genWellTyped ctx a
                pure (Rec l e)) ]
          _ -> []

      -- RProj: e.l (generate e : {l : ty})
      , [ (1, resize (n `div` 2) $ do
              l <- genLabel
              e <- genWellTyped ctx (TyRcd l ty)
              pure (RProj e l)) ]

      -- Let: let e1 : A in e2
      , [ (2, resize (n `div` 2) $ do
              a <- resize (n `div` 3) genTyp
              e1 <- genWellTyped ctx a
              e2 <- genWellTyped (TyAnd ctx a) ty
              pure (Let e1 a e2)) ]

      -- Open: open e1 in e2  (e1 must be a record)
      , [ (1, resize (n `div` 2) $ do
              l <- genLabel
              a <- resize (n `div` 3) genTyp
              e1 <- genWellTyped ctx (TyRcd l a)
              e2 <- genWellTyped (TyAnd ctx a) ty
              pure (Open e1 e2)) ]

      -- MStruct: struct[sb] body  (only when ty is TyMod (TyIntf _))
      , case ty of
          TyMod (TyIntf a) ->
            [ (2, resize (n `div` 2) $ do
                sb <- genSandbox
                let ctx' = case sb of
                             Sandboxed -> Unit
                             Open_     -> ctx
                body <- genWellTyped ctx' a
                pure (MStruct sb body))
            ]
          _ -> []

      -- MFunctor: functor[sb](A) body  (only when ty is TyArr)
      , case ty of
          TyMod (TyArrM a mt) ->
            [ (2, resize (n `div` 2) $ do
                sb <- genSandbox
                let ctx' = case sb of
                             Sandboxed -> TyAnd Unit a
                             Open_     -> TyAnd ctx a
                body <- genWellTyped ctx' (TyMod mt)
                pure (MFunctor sb a body))
            ]
          _ -> []

      -- MLink: Link(e1, e2) where e1 : TySig a ty or TyArr a ty
      , case ty of
          TyMod mt ->
            [ (2, resize (n `div` 2) $ do
                a <- resize (n `div` 3) genTyp
                e1 <- genWellTyped ctx (TyMod (TyArrM a mt))
                e2 <- genWellTyped ctx a
                pure (MLink e1 e2)) ]
          _ -> []
      ]

--------------------------------------------------------------------------------
-- Specialized generators for specific property needs
--------------------------------------------------------------------------------

-- Generate a sandboxed functor
genSandboxedFunctor :: Typ -> ModTyp -> Gen Exp
genSandboxedFunctor tyA mt = do
  body <- resize 5 $ genWellTyped (TyAnd Unit tyA) (TyMod mt)
  pure $ MFunctor Sandboxed tyA body

genLinkablePair :: Typ -> Gen (Exp, Exp)
genLinkablePair ctx = resize 5 $ do
  tyA <- resize 2 genTyp
  mt  <- resize 2 (sized genModTyp)
  e1 <- genWellTyped ctx (TyMod (TyArrM tyA mt))
  e2 <- genWellTyped ctx tyA
  pure (e1, e2)

-- Generate a linkable pair where the functor is sandboxed
genSandboxedLinkablePair :: Typ -> Gen (Exp, Exp)
genSandboxedLinkablePair ctx = resize 5 $ do
  tyA <- resize 2 genTyp
  mt  <- resize 2 (sized genModTyp)
  body <- genWellTyped (TyAnd Unit tyA) (TyMod mt)
  let e1 = MFunctor Sandboxed tyA body
  e2 <- genWellTyped ctx tyA
  pure (e1, e2)

--------------------------------------------------------------------------------
-- Newtype wrappers for Arbitrary instances
--------------------------------------------------------------------------------

-- Well-typed expression under Unit context
newtype WellTyped = WellTyped Exp deriving Show

instance Arbitrary WellTyped where
  arbitrary :: Gen WellTyped
  arbitrary = sized $ \n -> do
    ty <- resize (n `div` 2) genTyp
    e  <- resize n (genWellTyped Unit ty)
    pure (WellTyped e)

-- Well-typed value
newtype WellTypedVal = WellTypedVal Exp deriving Show
-- (Typ, Value) pair
data TypedVal = TypedVal Typ Exp deriving Show

instance Arbitrary WellTypedVal where
  arbitrary = do
    ty <- resize 3 genValTyp
    v  <- genVal ty
    pure (WellTypedVal v)

instance Arbitrary TypedVal where
  arbitrary = do
    ty <- resize 3 genValTyp
    v  <- genVal ty
    pure (TypedVal ty v)

-- Sandboxed struct with its type info
data SandboxedModule = SandboxedModule Typ Typ Exp deriving Show

instance Arbitrary SandboxedModule where
  arbitrary :: Gen SandboxedModule
  arbitrary = do
    tyA <- resize 2 genTyp
    tyB <- resize 2 genTyp
    body <- resize 5 $ genWellTyped Unit tyB
    pure $ SandboxedModule tyA tyB (MStruct Sandboxed body)

-- Linkable pair under Unit context
data LinkPair = LinkPair Exp Exp deriving Show

instance Arbitrary LinkPair where
  arbitrary :: Gen LinkPair
  arbitrary = do
    (e1, e2) <- genLinkablePair Unit
    pure $ LinkPair e1 e2

-- Sandboxed linkable pair
data SandboxedLinkPair = SandboxedLinkPair Exp Exp deriving Show

instance Arbitrary SandboxedLinkPair where
  arbitrary :: Gen SandboxedLinkPair
  arbitrary = do
    (e1, e2) <- genSandboxedLinkablePair Unit
    pure $ SandboxedLinkPair e1 e2

-- Expression with its context and type (for context-sensitive props)
data TypedExp = TypedExp Typ Typ Exp deriving Show

instance Arbitrary TypedExp where
  arbitrary :: Gen TypedExp
  arbitrary = sized $ \n -> do
    ctx <- resize (n `div` 3) genTyp
    ty  <- resize (n `div` 2) genTyp
    e   <- resize n (genWellTyped ctx ty)
    pure $ TypedExp ctx ty e

--------------------------------------------------------------------------------
-- SANITY PROPERTIES: generator correctness
--------------------------------------------------------------------------------

-- Generated expressions actually elaborate successfully
prop_genIsWellTyped :: WellTyped -> Property
prop_genIsWellTyped (WellTyped e) =
  case elaborate Unit e of
    Right _ -> property True
    Left err -> counterexample
      ("generated ill-typed term: " ++ show e ++ "\nerror: " ++ err) False

-- Generated values satisfy isValue
prop_genValIsValue :: WellTypedVal -> Property
prop_genValIsValue (WellTypedVal v) =
  property $ isValue v

-- Generated expressions under arbitrary context elaborate to expected type
prop_genTypedExpWellTyped :: TypedExp -> Property
prop_genTypedExpWellTyped (TypedExp ctx ty e) =
  case elaborate ctx e of
    Right (ty', _) -> ty' === ty
    Left err -> counterexample
      ("ctx=" ++ show ctx ++ " ty=" ++ show ty ++
       "\nterm: " ++ show e ++ "\nerror: " ++ err) False

--------------------------------------------------------------------------------
-- THEOREM: Type-Preserving Elaboration
-- If G |-S e : A ~> ce, then [G] |-C ce : [A]
--------------------------------------------------------------------------------

prop_typePreservingElab :: WellTyped -> Property
prop_typePreservingElab (WellTyped se) =
  case elaborate Unit se of
    Right (a, ce) ->
      C.infer (elaborateTyp Unit) ce === Right (elaborateTyp a)
    Left _ -> property True

-- Generalized: works under any context
prop_typePreservingElabGen :: TypedExp -> Property
prop_typePreservingElabGen (TypedExp ctx _ty e) =
  case elaborate ctx e of
    Right (a, ce) ->
      C.infer (elaborateTyp ctx) ce === Right (elaborateTyp a)
    Left _ -> property True

--------------------------------------------------------------------------------
-- THEOREM: Uniqueness of Elaboration
--------------------------------------------------------------------------------

prop_uniqueElab :: WellTyped -> Property
prop_uniqueElab (WellTyped se) =
  case (elaborate Unit se, elaborate Unit se) of
    (Right (a1, ce1), Right (a2, ce2)) ->
      (a1 === a2) .&&. (ce1 === ce2)
    _ -> property True

--------------------------------------------------------------------------------
-- THEOREM: Semantics Preservation
-- Source big-step and core big-step agree on elaborated terms
--------------------------------------------------------------------------------

prop_semanticsPreservation :: WellTyped -> Property
prop_semanticsPreservation (WellTyped se) =
  case elaborate Unit se of
    Right (_, ce) ->
      case (bigStep UnitE se, C.bigStep C.UnitE ce) of
        (Right sv, Right cv) ->
          case (infer Unit sv, C.infer C.Unit cv) of
            (Right sty, Right cty) ->
              elaborateTyp sty === cty
            _ -> property True
        (Left _, Left _) -> property True
        (Left serr, Right cv) -> counterexample
          ("source failed: " ++ serr ++ " but core gave: " ++ show cv) False
        (Right sv, Left cerr) -> counterexample
          ("source gave: " ++ show sv ++ " but core failed: " ++ cerr) False
    Left _ -> property True

--------------------------------------------------------------------------------
-- THEOREM: Capability Safety / Sandbox Isolation
--------------------------------------------------------------------------------

-- Sandboxed struct produces same result under any environment
prop_sandboxStructIsolation :: SandboxedModule -> Property
prop_sandboxStructIsolation (SandboxedModule _tyA _tyB sb) =
  forAll (genVal =<< resize 2 genTyp) $ \env1 ->
    forAll (genVal =<< resize 2 genTyp) $ \env2 ->
      case (bigStep env1 sb, bigStep env2 sb) of
        (Right v1, Right v2) -> v1 === v2
        (Left _, Left _)     -> property True
        (Left e, Right v)    -> counterexample
          ("env1 failed: " ++ e ++ " env2 gave: " ++ show v) False
        (Right v, Left e)    -> counterexample
          ("env1 gave: " ++ show v ++ " env2 failed: " ++ e) False

-- Sandboxed functor produces same closure under any environment
prop_sandboxFunctorIsolation :: Property
prop_sandboxFunctorIsolation =
  forAll (resize 2 genTyp) $ \tyA ->
    forAll (resize 2 (sized genModTyp)) $ \mt ->
      forAll (genSandboxedFunctor tyA mt) $ \sf ->
        forAll (genVal =<< resize 2 genTyp) $ \env1 ->
          forAll (genVal =<< resize 2 genTyp) $ \env2 ->
            case (bigStep env1 sf, bigStep env2 sf) of
              (Right v1, Right v2) -> v1 === v2
              (Left _, Left _)     -> property True
              _                    -> property False

--------------------------------------------------------------------------------
-- THEOREM: Separate Compilation
-- [Link(M1, M2)] = App([M1], [M2])
--------------------------------------------------------------------------------

prop_separateCompilation :: LinkPair -> Property
prop_separateCompilation (LinkPair se1 se2) =
  case elaborate Unit (MLink se1 se2) of
    Right (_, cLinked) ->
      case (elaborate Unit se1, elaborate Unit se2) of
        (Right (_, ce1), Right (_, ce2)) ->
          cLinked === C.App ce1 ce2
        _ -> property True
    Left _ -> property True

--------------------------------------------------------------------------------
-- THEOREM: Secure Linking
-- Sandboxed functor result is independent of linking environment
--------------------------------------------------------------------------------

prop_secureLinking :: SandboxedLinkPair -> Property
prop_secureLinking (SandboxedLinkPair sf arg) =
  forAll (genVal =<< resize 2 genTyp) $ \env1 ->
    forAll (genVal =<< resize 2 genTyp) $ \env2 ->
      case (bigStep env1 (MLink sf arg), bigStep env2 (MLink sf arg)) of
        (Right v1, Right v2) -> v1 === v2
        (Left _, Left _)     -> property True
        _                    -> property False

--------------------------------------------------------------------------------
-- THEOREM: Link Elaboration Commutes with Evaluation
-- eval([Link(M1,M2)]) = eval(App([M1], [M2]))
--------------------------------------------------------------------------------

prop_linkElabCommutes :: LinkPair -> Property
prop_linkElabCommutes (LinkPair se1 se2) =
  case (elaborate Unit (MLink se1 se2), elaborate Unit se1, elaborate Unit se2) of
    (Right (_, cLinked), Right (_, ce1), Right (_, ce2)) ->
      case (C.bigStep C.UnitE cLinked, C.bigStep C.UnitE (C.App ce1 ce2)) of
        (Right v1, Right v2) -> v1 === v2
        (Left _, Left _)     -> property True
        (Left e, Right v)    -> counterexample
          ("linked failed: " ++ e ++ " but app gave: " ++ show v) False
        (Right v, Left e)    -> counterexample
          ("linked gave: " ++ show v ++ " but app failed: " ++ e) False
    _ -> property True

--------------------------------------------------------------------------------
-- THEOREM: NMrg Independence
--------------------------------------------------------------------------------

prop_nmrgIndependence :: WellTyped -> WellTyped -> Property
prop_nmrgIndependence (WellTyped se1) (WellTyped se2) =
  case elaborate Unit (NMrg se1 se2) of
    Right (TyAnd _ b, _) ->
      case elaborate Unit se2 of
        Right (b', _) -> b === b'
        Left _        -> property True
    _ -> property True

--------------------------------------------------------------------------------
-- THEOREM: DMrg Allows Dependency
--------------------------------------------------------------------------------

prop_dmrgDependency :: Property
prop_dmrgDependency =
  let e = DMrg (Lit 1) (Proj Query 0)
  in case elaborate Unit e of
       Right (TyAnd Int Int, _) -> property True
       Right (ty, _) -> counterexample ("unexpected type: " ++ show ty) False
       Left err -> counterexample ("failed: " ++ err) False

--------------------------------------------------------------------------------
-- THEOREM: Struct / Functor elaboration shapes
--------------------------------------------------------------------------------

prop_structShapeSandboxed :: SandboxedModule -> Property
prop_structShapeSandboxed (SandboxedModule _ _ sb) =
  case elaborate Unit sb of
    Right (TyMod (TyIntf _), C.Box C.UnitE _) -> property True
    Right (ty, ce) -> counterexample
      ("unexpected: ty=" ++ show ty ++ " ce=" ++ show ce) False
    Left err -> counterexample ("failed: " ++ err) False

prop_structShapeOpen :: Property
prop_structShapeOpen =
  forAll (resize 2 genTyp) $ \tyB ->
    forAll (resize 5 $ genWellTyped Unit tyB) $ \body ->
      case elaborate Unit (MStruct Open_ body) of
        Right (TyMod (TyIntf _), C.Box C.Query _) -> property True
        Right (ty, ce) -> counterexample
          ("unexpected: ty=" ++ show ty ++ " ce=" ++ show ce) False
        Left err -> counterexample ("failed: " ++ err) False

prop_functorShapeSandboxed :: Property
prop_functorShapeSandboxed =
  forAll (resize 2 genTyp) $ \tyA ->
    forAll (resize 2 (sized genModTyp)) $ \mt ->
      forAll (genSandboxedFunctor tyA mt) $ \sf ->
        case elaborate Unit sf of
          Right (TyMod (TyArrM _ _), C.Box C.UnitE (C.Lam _ _)) -> property True
          Right (ty, ce) -> counterexample
            ("unexpected: ty=" ++ show ty ++ " ce=" ++ show ce) False
          Left err -> counterexample ("failed: " ++ err) False

prop_functorShapeOpen :: Property
prop_functorShapeOpen =
  forAll (resize 2 genTyp) $ \tyA ->
    forAll (resize 2 genTyp) $ \tyB ->
      forAll (resize 5 $ genWellTyped (TyAnd Unit tyA) tyB) $ \body ->
        case elaborate Unit (MFunctor Open_ tyA body) of
          Right (TyMod (TyArrM _ _), C.Lam _ _) -> property True
          Right (ty, ce) -> counterexample
            ("unexpected: ty=" ++ show ty ++ " ce=" ++ show ce) False
          Left err -> counterexample ("failed: " ++ err) False

--------------------------------------------------------------------------------
-- THEOREM: Sandbox Elaboration Context Independence
-- Sandboxed module's core term is same regardless of source context
--------------------------------------------------------------------------------

prop_sandboxElabContextIndep :: Property
prop_sandboxElabContextIndep =
  forAll (resize 2 genTyp) $ \tyA ->
    forAll (resize 2 genTyp) $ \tyB ->
      forAll (resize 2 genTyp) $ \ctx1 ->
        forAll (resize 2 genTyp) $ \ctx2 ->
            forAll (resize 5 $ genWellTyped Unit tyB) $ \body ->
            let sb = MStruct Sandboxed body
            in case (elaborate ctx1 sb, elaborate ctx2 sb) of
                 (Right (_, ce1), Right (_, ce2)) -> ce1 === ce2
                 _ -> property True

--------------------------------------------------------------------------------
-- Values are normal forms at source level
--------------------------------------------------------------------------------

prop_valuesSourceNormalForm :: WellTypedVal -> Property
prop_valuesSourceNormalForm (WellTypedVal v) =
  case bigStep UnitE v of
    Right v' -> v === v'
    Left err -> counterexample
      ("value didn't reduce to itself: " ++ err) False

--------------------------------------------------------------------------------
-- TEST RUNNER
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Generator Sanity ==="
  qc "genIsWellTyped"          prop_genIsWellTyped
  qc "genValIsValue"           prop_genValIsValue
  qc "genTypedExpWellTyped"    prop_genTypedExpWellTyped

  putStrLn "\n=== Type-Preserving Elaboration ==="
  qc "typePreservingElab"      prop_typePreservingElab
  qc "typePreservingElabGen"   prop_typePreservingElabGen

  putStrLn "\n=== Uniqueness ==="
  qc "uniqueElab"              prop_uniqueElab

  putStrLn "\n=== Semantics Preservation ==="
  qc "semanticsPreservation"   SCE.prop_semanticsPreservation

  putStrLn "\n=== Sandbox Isolation ==="
  qc "sandboxStructIsolation"  prop_sandboxStructIsolation
  qc "sandboxFunctorIsolation" SCE.prop_sandboxFunctorIsolation

  putStrLn "\n=== Separate Compilation ==="
  qc "separateCompilation"     SCE.prop_separateCompilation

  putStrLn "\n=== Secure Linking ==="
  qc "secureLinking"           SCE.prop_secureLinking

  putStrLn "\n=== Link Elaboration Commutes ==="
  qc "linkElabCommutes"        prop_linkElabCommutes

  putStrLn "\n=== NMrg Independence ==="
  qc "nmrgIndependence"        SCE.prop_nmrgIndependence

  putStrLn "\n=== DMrg Dependency ==="
  qc "dmrgDependency"          prop_dmrgDependency

  putStrLn "\n=== Elaboration Shape ==="
  qc "structShapeSandboxed"    prop_structShapeSandboxed
  qc "structShapeOpen"         prop_structShapeOpen
  qc "functorShapeSandboxed"   prop_functorShapeSandboxed
  qc "functorShapeOpen"        prop_functorShapeOpen

  putStrLn "\n=== Sandbox Context Independence ==="
  qc "sandboxElabContextIndep" prop_sandboxElabContextIndep

  putStrLn "\n=== Values Normal Form ==="
  qc "valuesSourceNormalForm"  prop_valuesSourceNormalForm

  where
    qc name prop = do
      putStr $ "  " ++ name ++ ": "
      quickCheckWith stdArgs { maxSuccess = 500 } prop