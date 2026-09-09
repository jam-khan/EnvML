module CoreFE.DeBruijnSpec (spec) where

import Test.Hspec
import qualified CoreFE.Named as N
import qualified CoreFE.Syntax as C
import CoreFE.DeBruijn (toNamelessExp, toNamelessTyp, toDeBruijn, toDeBruijnTyp)
import CoreFE.Check (check, infer)
import CoreFE.Eval (eval)

-- A literal environment, newest entry first (a Unit-rooted Merge/TMerge chain)
env :: [C.Entry] -> C.Exp
env = C.mkEnv

-- Abbreviations for the literal types and terms the tables repeat
cInt, cBool, cStr :: C.Typ
cInt = C.TyLit C.TyInt
cBool = C.TyLit C.TyBool
cStr = C.TyLit C.TyStr

nInt, nBool :: N.Typ
nInt = N.TyLit C.TyInt
nBool = N.TyLit C.TyBool

-- Helper to run full pipeline
runPipeline :: N.Exp -> Maybe (C.Exp, C.Typ, C.Exp)
runPipeline namedExp = do
  let namelessExp = toDeBruijn namedExp
  typ <- infer [] namelessExp
  result <- eval C.Unit namelessExp
  return (namelessExp, typ, result)

-- Test data
debruijnTests :: [(String, N.Exp, C.Exp, Maybe C.Typ, Maybe C.Exp)]
debruijnTests =
  [ -- Basic literals (1-3)
    ( "1. int literal"
    , N.Lit (C.LitInt 42)
    , C.Lit (C.LitInt 42)
    , Just (cInt)
    , Just (C.Lit (C.LitInt 42))
    )
  , ("2. bool literal", N.Lit (C.LitBool True), C.Lit (C.LitBool True), Just (cBool), Just (C.Lit (C.LitBool True)))
  , ("3. string literal", N.Lit (C.LitStr "hello"), C.Lit (C.LitStr "hello"), Just (cStr), Just (C.Lit (C.LitStr "hello")))

    -- Simple lambda and variables (4-8)
  , ( "4. identity lambda"
    , N.Lam "x" (N.Var "x")
    , C.Lam (C.Var 0)
    , Nothing  -- can't infer without annotation
    , Just (C.Clos C.Unit (C.Var 0))
    )
  , ( "5. annotated identity lambda"
    , N.Anno 
        (N.Lam "x" (N.Var "x")) 
        (N.TyArr (nInt) (nInt))
    , C.Anno 
        (C.Lam (C.Var 0)) 
        (C.TyArr (cInt) (cInt))
    , Just (C.TyArr (cInt) (cInt))
    , Just (C.Clos C.Unit (C.Var 0))
    )
  , ( "6. nested lambda - uses outer variable"
    , N.Lam "x" (N.Lam "y" (N.Var "x"))
    , C.Lam (C.Lam (C.Var 1))
    , Nothing
    , Just (C.Clos C.Unit (C.Lam (C.Var 1)))
    )
  , ( "7. nested lambda - uses inner variable"
    , N.Lam "x" (N.Lam "y" (N.Var "y"))
    , C.Lam (C.Lam (C.Var 0))
    , Nothing
    , Just (C.Clos C.Unit (C.Lam (C.Var 0)))
    )
  , ( "8. nested lambda - uses both variables"
    , N.Anno
        (N.Lam "x" (N.Lam "y" (N.App (N.Var "x") (N.Var "y"))))
        (N.TyArr 
          (N.TyArr (nInt) (nInt))
          (N.TyArr (nInt) (nInt)))
    , C.Anno
        (C.Lam (C.Lam (C.App (C.Var 1) (C.Var 0))))
        (C.TyArr 
          (C.TyArr (cInt) (cInt))
          (C.TyArr (cInt) (cInt)))
    , Just (C.TyArr 
          (C.TyArr (cInt) (cInt))
          (C.TyArr (cInt) (cInt)))
    , Just (C.Clos C.Unit (C.Lam (C.App (C.Var 1) (C.Var 0))))
    )

    -- Application (9-11)
  , ( "9. simple application"
    , N.App 
        (N.Anno 
          (N.Lam "x" (N.Var "x"))
          (N.TyArr (nInt) (nInt)))
        (N.Lit (C.LitInt 5))
    , C.App 
        (C.Anno 
          (C.Lam (C.Var 0))
          (C.TyArr (cInt) (cInt)))
        (C.Lit (C.LitInt 5))
    , Just (cInt)
    , Just (C.Lit (C.LitInt 5))
    )
  , ( "10. curried application"
    , N.App 
        (N.App 
          (N.Anno 
            (N.Lam "x" (N.Lam "y" (N.Var "x")))
            (N.TyArr (nInt) 
              (N.TyArr (nBool) (nInt))))
          (N.Lit (C.LitInt 42)))
        (N.Lit (C.LitBool True))
    , C.App 
        (C.App 
          (C.Anno 
            (C.Lam (C.Lam (C.Var 1)))
            (C.TyArr (cInt) 
              (C.TyArr (cBool) (cInt))))
          (C.Lit (C.LitInt 42)))
        (C.Lit (C.LitBool True))
    , Just (cInt)
    , Just (C.Lit (C.LitInt 42))
    )
  , ( "11. application returning second argument"
    , N.App 
        (N.App 
          (N.Anno 
            (N.Lam "x" (N.Lam "y" (N.Var "y")))
            (N.TyArr (nInt) 
              (N.TyArr (nBool) (nBool))))
          (N.Lit (C.LitInt 42)))
        (N.Lit (C.LitBool False))
    , C.App 
        (C.App 
          (C.Anno 
            (C.Lam (C.Lam (C.Var 0)))
            (C.TyArr (cInt) 
              (C.TyArr (cBool) (cBool))))
          (C.Lit (C.LitInt 42)))
        (C.Lit (C.LitBool False))
    , Just (cBool)
    , Just (C.Lit (C.LitBool False))
    )

    -- Type abstraction and application (12-15)
    -- Note: TLam containing Lam cannot be inferred, only checked
  , ( "12. polymorphic identity (annotated)"
    , N.Anno
        (N.TLam "a" (N.Lam "x" (N.Var "x")))
        (N.TyAll "a" (N.TyArr (N.TyVar "a") (N.TyVar "a")))
    , C.Anno
        (C.TLam (C.Lam (C.Var 0)))
        (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0)))
    , Just (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0)))
    , Just (C.TClos C.Unit (C.Lam (C.Var 0)))
    )
  , ( "13. type application of polymorphic identity (annotated)"
    , N.TApp 
        (N.Anno
          (N.TLam "a" (N.Lam "x" (N.Var "x")))
          (N.TyAll "a" (N.TyArr (N.TyVar "a") (N.TyVar "a"))))
        (nInt)
    , C.TApp 
        (C.Anno
          (C.TLam (C.Lam (C.Var 0)))
          (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0))))
        (cInt)
    , Just (C.TySubstT (cInt) 
            (C.TyArr (C.TyVar 0) (C.TyVar 0)))
    , Just (C.Clos (env [C.EntT (C.TyBoxT [] (cInt))]) 
            (C.Var 0))
    )
  , ( "14. nested type abstraction (annotated)"
    , N.Anno
        (N.TLam "a" (N.TLam "b" (N.Lam "x" (N.Var "x"))))
        (N.TyAll "a" (N.TyAll "b" (N.TyArr (N.TyVar "b") (N.TyVar "b"))))
    , C.Anno
        (C.TLam (C.TLam (C.Lam (C.Var 0))))
        (C.TyAll (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0))))
    , Just (C.TyAll (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0))))
    , Just (C.TClos C.Unit (C.TLam (C.Lam (C.Var 0))))
    )
  , ( "15. type variable in type annotation"
    , N.TLam "a" 
        (N.Anno 
          (N.Lam "x" (N.Var "x"))
          (N.TyArr (N.TyVar "a") (N.TyVar "a")))
    , C.TLam 
        (C.Anno 
          (C.Lam (C.Var 0))
          (C.TyArr (C.TyVar 0) (C.TyVar 0)))
    , Just (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0)))
    , Just (C.TClos C.Unit 
        (C.Anno 
          (C.Lam (C.Var 0))
          (C.TyArr (C.TyVar 0) (C.TyVar 0))))
    )

    -- Records (16-18)
  , ( "16. simple record"
    , N.Rec "x" (N.Lit (C.LitInt 42))
    , C.Rec "x" (C.Lit (C.LitInt 42))
    , Just (C.TyRcd "x" (cInt))
    , Just (C.Rec "x" (C.Lit (C.LitInt 42)))
    )
  , ( "17. record projection via FEnv"
    , N.RProj 
        (N.FEnv [N.ExpE "x" (N.Rec "val" (N.Lit (C.LitInt 42)))])
        "val"
    , C.RProj 
        (env [C.EntE (C.Rec "val" (C.Lit (C.LitInt 42)))])
        "val"
    , Just (cInt)
    , Just (C.Lit (C.LitInt 42))
    )
  , ( "18. record with lambda"
    , N.Rec "f" 
        (N.Anno 
          (N.Lam "x" (N.Var "x"))
          (N.TyArr (nInt) (nInt)))
    , C.Rec "f" 
        (C.Anno 
          (C.Lam (C.Var 0))
          (C.TyArr (cInt) (cInt)))
    , Just (C.TyRcd "f" 
        (C.TyArr (cInt) (cInt)))
    , Just (C.Rec "f" (C.Clos C.Unit (C.Var 0)))
    )

    -- First-class environments - basic (19-22)
  , ("19. empty environment", N.FEnv [], env [], Just (C.TyEnvt []), Just (env []))
  , ( "20. environment with single ExpE"
    , N.FEnv [N.ExpE "x" (N.Lit (C.LitInt 42))]
    , env [C.EntE (C.Lit (C.LitInt 42))]
    , Just (C.TyEnvt [C.Type (cInt)])
    , Just (env [C.EntE (C.Lit (C.LitInt 42))])
    )
  , ( "21. environment with multiple ExpE"
    , N.FEnv 
        [ N.ExpE "x" (N.Lit (C.LitInt 1))
        , N.ExpE "y" (N.Lit (C.LitInt 2))
        ]
    , env
        [ C.EntE (C.Lit (C.LitInt 1))
        , C.EntE (C.Lit (C.LitInt 2))
        ]
    , Just (C.TyEnvt 
        [ C.Type (cInt)
        , C.Type (cInt)
        ])
    , Just (env
        [ C.EntE (C.Lit (C.LitInt 1))
        , C.EntE (C.Lit (C.LitInt 2))
        ])
    )
  , ( "22. environment with TypE"
    , N.FEnv [N.TypE "t" (nInt)]
    , env [C.EntT (cInt)]
    , Just (C.TyEnvt [C.TypeEq (cInt)])
    , Just (env [C.EntT (C.TyBoxT [] (cInt))])
    )

    -- First-class environments - scoping (23-26)
  , ( "23. environment entry references later entry"
    , N.FEnv 
        [ N.ExpE "x" (N.Var "y")
        , N.ExpE "y" (N.Lit (C.LitInt 42))
        ]
    , env
        [ C.EntE (C.Var 0)  -- x sees y at index 0
        , C.EntE (C.Lit (C.LitInt 42))
        ]
    , Just (C.TyEnvt 
        [ C.Type (cInt)
        , C.Type (cInt)
        ])
    , Just (env
        [ C.EntE (C.Lit (C.LitInt 42))
        , C.EntE (C.Lit (C.LitInt 42))
        ])
    )
  , ( "24. environment with three entries, first references third"
    , N.FEnv 
        [ N.ExpE "x" (N.Var "z")
        , N.ExpE "y" (N.Lit (C.LitInt 1))
        , N.ExpE "z" (N.Lit (C.LitInt 2))
        ]
    , env
        [ C.EntE (C.Var 1)  -- x sees z at index 1 (y=0, z=1)
        , C.EntE (C.Lit (C.LitInt 1))
        , C.EntE (C.Lit (C.LitInt 2))
        ]
    , Just (C.TyEnvt 
        [ C.Type (cInt)
        , C.Type (cInt)
        , C.Type (cInt)
        ])
    , Just (env
        [ C.EntE (C.Lit (C.LitInt 2))
        , C.EntE (C.Lit (C.LitInt 1))
        , C.EntE (C.Lit (C.LitInt 2))
        ])
    )
  , ( "25. environment with second references third"
    , N.FEnv 
        [ N.ExpE "x" (N.Lit (C.LitInt 0))
        , N.ExpE "y" (N.Var "z")
        , N.ExpE "z" (N.Lit (C.LitInt 99))
        ]
    , env
        [ C.EntE (C.Lit (C.LitInt 0))
        , C.EntE (C.Var 0)  -- y sees z at index 0
        , C.EntE (C.Lit (C.LitInt 99))
        ]
    , Just (C.TyEnvt 
        [ C.Type (cInt)
        , C.Type (cInt)
        , C.Type (cInt)
        ])
    , Just (env
        [ C.EntE (C.Lit (C.LitInt 0))
        , C.EntE (C.Lit (C.LitInt 99))
        , C.EntE (C.Lit (C.LitInt 99))
        ])
    )
  , ( "26. environment with mixed ExpE and TypE"
    , N.FEnv 
        [ N.ExpE "x" (N.Lit (C.LitInt 1))
        , N.TypE "t" (nBool)
        , N.ExpE "y" (N.Lit (C.LitInt 2))
        ]
    , env
        [ C.EntE (C.Lit (C.LitInt 1))
        , C.EntT (cBool)
        , C.EntE (C.Lit (C.LitInt 2))
        ]
    , Just (C.TyEnvt 
        [ C.Type (cInt)
        , C.TypeEq (cBool)
        , C.Type (cInt)
        ])
    -- Eval result: TypE gets wrapped in TyBoxT with c2g of (rest ++ env)
    -- For the TypE at position 1, c2g of [ExpE (Lit 2)] ++ [] = []
    , Just (env
        [ C.EntE (C.Lit (C.LitInt 1))
        , C.EntT (C.TyBoxT [] (cBool))
        , C.EntE (C.Lit (C.LitInt 2))
        ])
    )

    -- Mode and mvar (27-29)
  , ( "27. ModE wraps in FEnv containing record"
    , N.FEnv [N.ModE "m" (N.Lit (C.LitInt 42))]
    , env [C.EntE (C.Rec "m" (C.Lit (C.LitInt 42)))]
    , Just (C.TyEnvt [C.Type (C.TyRcd "m" (cInt))])
    , Just (env [C.EntE (C.Rec "m" (C.Lit (C.LitInt 42)))])
    )
  , ( "28. ModE projection via RProj on FEnv"
    -- To project from ModE, we need to go through FEnv and RProj
    , N.RProj 
        (N.FEnv [N.ModE "m" (N.Lit (C.LitInt 42))])
        "m"
    , C.RProj 
        (env [C.EntE (C.Rec "m" (C.Lit (C.LitInt 42)))])
        "m"
    , Just (cInt)
    , Just (C.Lit (C.LitInt 42))
    )
  , ( "29. Var referencing ExpE stays as Var"
    , N.FEnv 
        [ N.ExpE "result" (N.Var "x")  -- x is ExpE, stays as Var
        , N.ExpE "x" (N.Lit (C.LitInt 42))
        ]
    , env
        [ C.EntE (C.Var 0)
        , C.EntE (C.Lit (C.LitInt 42))
        ]
    , Just (C.TyEnvt 
        [ C.Type (cInt)
        , C.Type (cInt)
        ])
    , Just (env
        [ C.EntE (C.Lit (C.LitInt 42))
        , C.EntE (C.Lit (C.LitInt 42))
        ])
    )

    -- Box and closures (30-32)
  , ( "30. box with simple environment"
    , N.Box 
        [N.ExpE "x" (N.Lit (C.LitInt 42))]
        (N.Var "x")
    , C.Box
        (env [C.EntE (C.Lit (C.LitInt 42))])
        (C.Var 0)
    , Just (C.TyBoxT 
        [C.Type (cInt)]
        (cInt))
    , Just (C.Lit (C.LitInt 42))
    )
  , ( "31. closure with environment"
    , N.Clos 
        [N.ExpE "captured" (N.Lit (C.LitInt 10))]
        (N.Var "captured")
    , C.Clos
        (env [C.EntE (C.Lit (C.LitInt 10))])
        (C.Var 0)
    , Nothing  -- closures need checking, not inference
    , Just (C.Clos
        (env [C.EntE (C.Lit (C.LitInt 10))])
        (C.Var 0))
    )
  , ( "32. tclos with type environment"
    , N.TClos 
        [N.TypE "t" (nInt)]
        (N.Lam "x" (N.Var "x"))
    , C.TClos
        (env [C.EntT (cInt)])
        (C.Lam (C.Var 0))
    , Nothing  -- closures need checking
    , Just (C.TClos
        (env [C.EntT (cInt)])
        (C.Lam (C.Var 0)))
    )

    -- Complex type translations (33-35)
  , ( "33. forall type in annotation"
    , N.Anno 
        (N.TLam "a" (N.Lam "x" (N.Var "x")))
        (N.TyAll "a" (N.TyArr (N.TyVar "a") (N.TyVar "a")))
    , C.Anno 
        (C.TLam (C.Lam (C.Var 0)))
        (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0)))
    , Just (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0)))
    , Just (C.TClos C.Unit (C.Lam (C.Var 0)))
    )
  , ( "34. nested forall types"
    , N.Anno 
        (N.TLam "a" (N.TLam "b" (N.Lam "x" (N.Var "x"))))
        (N.TyAll "a" (N.TyAll "b" (N.TyArr (N.TyVar "b") (N.TyVar "b"))))
    , C.Anno 
        (C.TLam (C.TLam (C.Lam (C.Var 0))))
        (C.TyAll (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0))))
    , Just (C.TyAll (C.TyAll (C.TyArr (C.TyVar 0) (C.TyVar 0))))
    , Just (C.TClos C.Unit (C.TLam (C.Lam (C.Var 0))))
    )
  , ( "35. forall referencing outer type variable"
    , N.Anno 
        (N.TLam "a" (N.TLam "b" (N.Lam "x" (N.Var "x"))))
        (N.TyAll "a" (N.TyAll "b" (N.TyArr (N.TyVar "a") (N.TyVar "a"))))
    , C.Anno 
        (C.TLam (C.TLam (C.Lam (C.Var 0))))
        (C.TyAll (C.TyAll (C.TyArr (C.TyVar 1) (C.TyVar 1))))
    , Just (C.TyAll (C.TyAll (C.TyArr (C.TyVar 1) (C.TyVar 1))))
    , Just (C.TClos C.Unit (C.TLam (C.Lam (C.Var 0))))
    )
  ]

-- Type-only tests

typeDebruijnTests :: [(String, N.Typ, C.Typ)]
typeDebruijnTests =
  [ ( "type: simple literal"
    , nInt
    , cInt
    )
  , ( "type: arrow"
    , N.TyArr (nInt) (nBool)
    , C.TyArr (cInt) (cBool)
    )
  , ( "type: forall with variable"
    , N.TyAll "a" (N.TyVar "a")
    , C.TyAll (C.TyVar 0)
    )
  , ( "type: nested forall"
    , N.TyAll "a" (N.TyAll "b" (N.TyArr (N.TyVar "a") (N.TyVar "b")))
    , C.TyAll (C.TyAll (C.TyArr (C.TyVar 1) (C.TyVar 0)))
    )
  , ( "type: record type"
    , N.TyRcd "label" (nInt)
    , C.TyRcd "label" (cInt)
    )
  ]
-- Spec

spec :: Spec
spec = do
  describe "De Bruijn Transformation" $ do
    describe "Expression transformation" $ do
      mapM_ mkDebruijnTest debruijnTests
    
    describe "Type transformation" $ do
      mapM_ mkTypeTest typeDebruijnTests

  where
    mkDebruijnTest (name, namedExp, expectedNameless, expectedType, expectedResult) =
      describe name $ do
        it "transforms to correct nameless form" $
          toDeBruijn namedExp `shouldBe` expectedNameless
        
        case expectedType of
          Just typ -> 
            it "type checks correctly" $
              infer [] (toDeBruijn namedExp) `shouldBe` Just typ
          Nothing ->
            it "type inference not expected (skipped)" $
              True `shouldBe` True  -- trivial assertion
        
        case expectedResult of
          Just result ->
            it "evaluates correctly" $
              eval C.Unit (toDeBruijn namedExp) `shouldBe` Just result
          Nothing ->
            it "evaluation not expected (skipped)" $
              True `shouldBe` True  -- trivial assertion
    
    mkTypeTest (name, namedTyp, expectedNameless) =
      it name $
        toDeBruijnTyp namedTyp `shouldBe` expectedNameless