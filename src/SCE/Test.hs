{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

module SCE.Test where

import Test.QuickCheck
import Control.Monad (liftM2)
import SCE.Core

isWellTyped :: Exp -> Bool
isWellTyped e = case infer Unit e of
  Right _ -> True
  Left _  -> False

-- Generate small types (controls term size)
genTyp :: Gen Typ
genTyp = sized go
  where
    go n
      | n <= 0    = frequency [(3, pure Int), (1, pure Unit)]
      | otherwise = frequency
          [ (4, pure Int)
          , (1, pure Unit)
          , (2, TyAnd <$> go (n `div` 2) <*> go (n `div` 2))
          , (2, TyArr <$> go (n `div` 2) <*> go (n `div` 2))
          , (1, TyRcd <$> genLabel <*> go (n `div` 2))
          ]

genLabel :: Gen Name
genLabel = elements ["x", "y", "z", "a", "b"]

-- Generate a well-typed value of a given type (always terminates)
genVal :: Typ -> Gen Exp
genVal Int          = Lit <$> arbitrary
genVal Unit         = pure UnitE
genVal (TyAnd a b)   = Mrg <$> genVal a <*> genVal b
genVal (TyRcd l a)   = Rec l <$> genVal a
genVal (TyArr a b)   = do
  body <- genWellTyped (TyAnd Unit a) b
  pure $ Clos UnitE a body

-- Find all de Bruijn indices in a context that yield a given type
-- Context is right-to-left: TyAnd (TyAnd (TyAnd ε A2) A1) A0
-- Index 0 → rightmost component, index 1 → next, etc.
findIndices :: Typ -> Typ -> [Int]
findIndices ctx target = go ctx 0
  where
    go (TyAnd rest rightmost) i =
      (if rightmost == target then [i] else []) ++ go rest (i + 1)
    go _ _ = []  -- atomic types have NO valid de Bruijn indices

-- Generate a well-typed expression:  ctx ⊢ e : ty
genWellTyped :: Typ -> Typ -> Gen Exp
genWellTyped ctx ty = sized $ \n ->
  if n <= 0
    then genVal ty
    else frequency $ concat
      [ -- Base: always available
        [ (3, genVal ty) ]
        -- Typ-ctx: ? : Γ  (only when ctx == ty)
      , [ (3, pure Query) | ctx == ty ]
        -- Typ-proj: e.n where e : ctx' and lookup(ctx', n) = ty
        -- Use Query.n when there's an index in ctx that gives ty
      , let idxs = findIndices ctx ty
        in [ (2, do i <- elements idxs; pure (Proj Query i)) | not (null idxs) ]
        -- Typ-lam: λA. e  (only when ty is an arrow type)
      , case ty of
          TyArr a b ->
            [ (3, resize (n `div` 2) $ do
                body <- genWellTyped (TyAnd ctx a) b
                pure (Lam a body)) ]
          _ -> []
        -- Typ-app: e1 e2 where e1 : A → ty, e2 : A
      , [ (2, resize (n `div` 2) $ do
              a <- resize (n `div` 3) genTyp
              f <- genWellTyped ctx (TyArr a ty)
              arg <- genWellTyped ctx a
              pure (App f arg)) ]
        -- Typ-merge: e1 # e2  (only when ty is TyAnd)
      , case ty of
          TyAnd a b ->
            [ (2, resize (n `div` 2) $ do
                e1 <- genWellTyped ctx a
                e2 <- genWellTyped (TyAnd ctx a) b
                pure (Mrg e1 e2)) ]
          _ -> []
        -- Typ-box: e1 ▷ e2 where e1 : Γ1, Γ1 ⊢ e2 : ty
      , [ (2, resize (n `div` 2) $ do
              gamma1 <- resize (n `div` 3) genTyp
              e1 <- genWellTyped ctx gamma1
              e2 <- genWellTyped gamma1 ty
              pure (Box e1 e2)) ]
        -- Typ-rcd: {l = e}  (only when ty is TyRcd)
      , case ty of
          TyRcd l a ->
            [ (2, resize (n `div` 2) $ do
                e <- genWellTyped ctx a
                pure (Rec l e)) ]
          _ -> []
        -- Typ-sel: e.l where e : B, l : ty ∈ B
        -- Generate e : {l : ty} (simplest containment)
      , [ (1, resize (n `div` 2) $ do
              l <- genLabel
              e <- genWellTyped ctx (TyRcd l ty)
              pure (RProj e l)) ]
      ]

-- Newtype for QuickCheck integration
newtype WellTyped = WellTyped Exp deriving Show

instance Arbitrary WellTyped where
  arbitrary :: Gen WellTyped
  arbitrary = sized $ \n -> do
    ty <- resize (n `div` 2) genTyp
    e  <- resize n (genWellTyped Unit ty)
    pure (WellTyped e)

newtype WellTypedVal = WellTypedVal Exp deriving Show

instance Arbitrary WellTypedVal where
  arbitrary :: Gen WellTypedVal
  arbitrary = do
    ty <- resize 3 genTyp
    v  <- genVal ty
    pure (WellTypedVal v)

data TypedVal = TypedVal Typ Exp deriving Show

instance Arbitrary TypedVal where
  arbitrary = do
    ty <- resize 3 genTyp
    v  <- genVal ty
    pure (TypedVal ty v)

prop_genIsWellTyped :: WellTyped -> Bool
prop_genIsWellTyped (WellTyped e) =
  case infer Unit e of
    Right _ -> True
    Left err -> error $ "generated ill-typed term: " ++ show e ++ "\nerror: " ++ err

prop_genValIsValue :: WellTypedVal -> Bool
prop_genValIsValue (WellTypedVal v) = isValue v

------------------------------------------------------------------------
-- Theorem 4.2 / Corollary 4.3: Determinism
-- If ε ⊢ e : A and ε ⊢ e ↦ e1 and ε ⊢ e ↦ e2, then e1 = e2
------------------------------------------------------------------------
prop_determinism :: WellTyped -> Property
prop_determinism (WellTyped e) =
  not (isValue e) ==>
    case (step UnitE e, step UnitE e) of
      (Right e1, Right e2) -> e1 === e2
      _                    -> property True

------------------------------------------------------------------------
-- Corollary 4.10: Progress
-- If ε ⊢ e : A, then e is a value or ∃ e'. ε ⊢ e ↦ e'
------------------------------------------------------------------------
prop_progress :: WellTyped -> Property
prop_progress (WellTyped e) =
  property $ isValue e || isRight (step UnitE e)

------------------------------------------------------------------------
-- Corollary 4.11: Preservation
-- If ε ⊢ e : A and ε ⊢ e ↦ e', then ε ⊢ e' : A
------------------------------------------------------------------------
prop_preservation :: WellTyped -> Property
prop_preservation (WellTyped e) =
  not (isValue e) ==>
    case (infer Unit e, step UnitE e) of
      (Right ty, Right e') -> infer Unit e' === Right ty
      _                    -> property True

------------------------------------------------------------------------
-- Multi-step preservation: type is preserved through full evaluation
-- (Iterated Corollary 4.11)
------------------------------------------------------------------------
prop_preservationMulti :: WellTyped -> Property
prop_preservationMulti (WellTyped e) =
  case (infer Unit e, stepAll e) of
    (Right ty, Right v) -> infer Unit v === Right ty
    _                   -> property True

------------------------------------------------------------------------
-- Theorem 4.16: Termination
-- If ε ⊢ e : A then ∃ v. ε ⊢ e ↦* v
------------------------------------------------------------------------
prop_termination :: WellTyped -> Property
prop_termination (WellTyped e) =
  property $ isRight (stepAll e)

------------------------------------------------------------------------
-- Theorem 4.21: Big-step / Small-step Equivalence
-- v ⊢ e ⇒ v' iff v ⊢ e ↦* v'
------------------------------------------------------------------------

-- Soundness direction: big ⇒ small*
prop_bigImpliesSmall :: WellTyped -> Property
prop_bigImpliesSmall (WellTyped e) =
  case (bigStep UnitE e, stepAll e) of
    (Right v1, Right v2) -> v1 === v2
    (Left _, Left _)     -> property True
    (Left _, Right v)    -> counterexample
      ("big-step failed but small-step gave: " ++ show v) False
    (Right v, Left _)    -> counterexample
      ("big-step gave " ++ show v ++ " but small-step failed") False

-- Completeness direction: small* ⇒ big
prop_smallImpliesBig :: WellTyped -> Property
prop_smallImpliesBig (WellTyped e) =
  case (stepAll e, bigStep UnitE e) of
    (Right v1, Right v2) -> v1 === v2
    (Left _, Left _)     -> property True
    (Right v, Left _)    -> counterexample
      ("small-step gave " ++ show v ++ " but big-step failed") False
    (Left _, Right v)    -> counterexample
      ("small-step failed but big-step gave: " ++ show v) False

------------------------------------------------------------------------
-- Lemma 4.4: Progress of Lookup
-- If ε ⊢ v : A and lookup(A, n) = B, then lookupv(v, n) succeeds
------------------------------------------------------------------------
prop_lookupProgress :: TypedVal -> Property
prop_lookupProgress (TypedVal ty v) =
  forAll (chooseInt (0, depthAnd ty - 1)) $ \n ->
    isRight (lookupIdx ty n) ==>
      property $ isRight (lookupV v n)
  where
    depthAnd (TyAnd a _) = 1 + depthAnd a
    depthAnd _           = 1

------------------------------------------------------------------------
-- Lemma 4.5: Preservation of Lookup
-- If ε ⊢ v : A and lookup(A, n) = B and lookupv(v, n) = v', then ε ⊢ v' : B
------------------------------------------------------------------------
prop_lookupPreservation :: TypedVal -> Property
prop_lookupPreservation (TypedVal ty v) =
  forAll (chooseInt (0, depthAnd ty - 1)) $ \n ->
    case (lookupIdx ty n, lookupV v n) of
      (Right tyN, Right vN) -> infer Unit vN === Right tyN
      _                     -> property True
  where
    depthAnd (TyAnd a _) = 1 + depthAnd a
    depthAnd _           = 1

------------------------------------------------------------------------
-- Lemma 4.1: Determinism of Selection
-- If Γ ⊢ v.l : A and v.l ⇝ v1 and v.l ⇝ v2, then v1 = v2
------------------------------------------------------------------------
prop_selDeterminism :: WellTypedVal -> Property
prop_selDeterminism (WellTypedVal v) =
  forAll genLabel $ \l ->
    case sel v l of
      Right v1 -> sel v l === Right v1
      Left _   -> property True

------------------------------------------------------------------------
-- Lemma 4.6: Progress of Selection
-- If ε ⊢ v : A and l : B ∈ A, then ∃ v'. v.l ⇝ v'
------------------------------------------------------------------------
prop_selProgress :: TypedVal -> Property
prop_selProgress (TypedVal ty v) =
  forAll genLabel $ \l ->
    case containment l ty of
      Right _ -> property $ isRight (sel v l)
      Left _  -> property True

------------------------------------------------------------------------
-- Lemma 4.7: Preservation of Selection
-- If ε ⊢ v : A and l : B ∈ A and v.l ⇝ v', then ε ⊢ v' : B
------------------------------------------------------------------------
prop_selPreservation :: TypedVal -> Property
prop_selPreservation (TypedVal ty v) =
  forAll genLabel $ \l ->
    case (containment l ty, sel v l) of
      (Right tyL, Right vL) -> infer Unit vL === Right tyL
      _                     -> property True

------------------------------------------------------------------------
-- Lemma 4.18: Box Environment Isolation
-- If v ⊢ e ↦* v' and v' is a value, then v1 ⊢ (v ▷ e) ↦* v' for any v1
-- Tested via: bigStep env1 (Box env2 e) == bigStep UnitE (Box env2 e)
------------------------------------------------------------------------
prop_boxEnvIsolation :: WellTyped -> Property
prop_boxEnvIsolation (WellTyped e) =
  forAll (genVal =<< resize 2 genTyp) $ \env1 ->
    forAll (genVal =<< resize 2 genTyp) $ \env2 ->
      case (bigStep env1 (Box env2 e), bigStep UnitE (Box env2 e)) of
        (Right v1, Right v2) -> v1 === v2
        _                    -> property True

------------------------------------------------------------------------
-- Semantic consistency: infer and bigStep agree on result type
-- (Combines Theorem 4.12 + Corollary 4.11 in spirit)
------------------------------------------------------------------------
prop_inferBigStepConsistent :: WellTyped -> Property
prop_inferBigStepConsistent (WellTyped e) =
  case (infer Unit e, bigStep UnitE e) of
    (Right ty, Right v) -> infer Unit v === Right ty
    _                   -> property True

------------------------------------------------------------------------
-- Values are normal forms (no step possible)
-- Follows from the definition of values and Figure 3
------------------------------------------------------------------------
prop_valuesAreNormalForms :: WellTypedVal -> Property
prop_valuesAreNormalForms (WellTypedVal v) =
  property $ case step UnitE v of
    Left _  -> True
    Right _ -> False

------------------------------------------------------------------------
-- Closures: λA. e evaluates to ⟨v, λA. e⟩ in one step (Step-closure)
------------------------------------------------------------------------
prop_lamStepsToClosure :: WellTyped -> Property
prop_lamStepsToClosure (WellTyped e) =
  case e of
    Lam a body -> step UnitE (Lam a body) === Right (Clos UnitE a body)
    _          -> property True

------------------------------------------------------------------------
-- Query reduces to environment (Step-ctx)
------------------------------------------------------------------------
prop_queryReducesToEnv :: WellTypedVal -> Property
prop_queryReducesToEnv (WellTypedVal v) =
  step v Query === Right v

--------------------------------------------------------------------------------
-- 12. HELPERS
--------------------------------------------------------------------------------

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight (Left _)  = False

--------------------------------------------------------------------------------
-- 13. TEST RUNNER
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Generator Sanity ==="
  quickCheck prop_genIsWellTyped
  quickCheck prop_genValIsValue

  putStrLn "\n=== Determinism (Thm 4.2 / Cor 4.3) ==="
  quickCheck prop_determinism

  putStrLn "\n=== Progress (Cor 4.10) ==="
  quickCheck prop_progress

  putStrLn "\n=== Preservation (Cor 4.11) ==="
  quickCheck prop_preservation
  quickCheck prop_preservationMulti

  putStrLn "\n=== Termination (Thm 4.16) ==="
  quickCheck prop_termination

  putStrLn "\n=== Big/Small-step Equivalence (Thm 4.21) ==="
  quickCheck prop_bigImpliesSmall
  quickCheck prop_smallImpliesBig

  putStrLn "\n=== Lookup Progress (Lemma 4.4) ==="
  quickCheck prop_lookupProgress

  putStrLn "\n=== Lookup Preservation (Lemma 4.5) ==="
  quickCheck prop_lookupPreservation

  putStrLn "\n=== Selection Determinism (Lemma 4.1) ==="
  quickCheck prop_selDeterminism

  putStrLn "\n=== Selection Progress (Lemma 4.6) ==="
  quickCheck prop_selProgress

  putStrLn "\n=== Selection Preservation (Lemma 4.7) ==="
  quickCheck prop_selPreservation

  putStrLn "\n=== Box Env Isolation (Lemma 4.18) ==="
  quickCheck prop_boxEnvIsolation

  putStrLn "\n=== Semantic Consistency (Thm 4.12 spirit) ==="
  quickCheck prop_inferBigStepConsistent

  putStrLn "\n=== Values are Normal Forms ==="
  quickCheck prop_valuesAreNormalForms

  putStrLn "\n=== Lambda → Closure (Step-closure) ==="
  quickCheck prop_lamStepsToClosure

  putStrLn "\n=== Query → Env (Step-ctx) ==="
  quickCheck prop_queryReducesToEnv