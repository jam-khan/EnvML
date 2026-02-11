module CoreFE.DeBruijnSpec (spec) where

import Test.Hspec
import qualified CoreFE.Named as Named
import qualified CoreFE.Syntax as Nameless
import CoreFE.DeBruijn (toNamelessExp, toNamelessTyp, toDeBruijn, toDeBruijnTyp)
import CoreFE.Check (check, infer)
import CoreFE.Eval (eval)

-- Helper to run full pipeline
runPipeline :: Named.Exp -> Maybe (Nameless.Exp, Nameless.Typ, Nameless.Exp)
runPipeline namedExp = do
  let namelessExp = toDeBruijn namedExp
  typ <- infer [] namelessExp
  result <- eval [] namelessExp
  return (namelessExp, typ, result)

-- ============================================================================
-- Test Data
-- ============================================================================
debruijnTests :: [(String, Named.Exp, Nameless.Exp, Maybe Nameless.Typ, Maybe Nameless.Exp)]
debruijnTests =
  [ -- ==========================================================================
    -- Basic Literals (1-3)
    -- ==========================================================================
    ( "1. int literal"
    , Named.Lit (Nameless.LitInt 42)
    , Nameless.Lit (Nameless.LitInt 42)
    , Just (Nameless.TyLit Nameless.TyInt)
    , Just (Nameless.Lit (Nameless.LitInt 42))
    )
  , ( "2. bool literal"
    , Named.Lit (Nameless.LitBool True)
    , Nameless.Lit (Nameless.LitBool True)
    , Just (Nameless.TyLit Nameless.TyBool)
    , Just (Nameless.Lit (Nameless.LitBool True))
    )
  , ( "3. string literal"
    , Named.Lit (Nameless.LitStr "hello")
    , Nameless.Lit (Nameless.LitStr "hello")
    , Just (Nameless.TyLit Nameless.TyStr)
    , Just (Nameless.Lit (Nameless.LitStr "hello"))
    )

    -- ==========================================================================
    -- Simple Lambda and Variables (4-8)
    -- ==========================================================================
  , ( "4. identity lambda"
    , Named.Lam "x" (Named.Var "x")
    , Nameless.Lam (Nameless.Var 0)
    , Nothing  -- can't infer without annotation
    , Just (Nameless.Clos [] (Nameless.Var 0))
    )
  , ( "5. annotated identity lambda"
    , Named.Anno 
        (Named.Lam "x" (Named.Var "x")) 
        (Named.TyArr (Named.TyLit Nameless.TyInt) (Named.TyLit Nameless.TyInt))
    , Nameless.Anno 
        (Nameless.Lam (Nameless.Var 0)) 
        (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt))
    , Just (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt))
    , Just (Nameless.Clos [] (Nameless.Var 0))
    )
  , ( "6. nested lambda - uses outer variable"
    , Named.Lam "x" (Named.Lam "y" (Named.Var "x"))
    , Nameless.Lam (Nameless.Lam (Nameless.Var 1))
    , Nothing
    , Just (Nameless.Clos [] (Nameless.Lam (Nameless.Var 1)))
    )
  , ( "7. nested lambda - uses inner variable"
    , Named.Lam "x" (Named.Lam "y" (Named.Var "y"))
    , Nameless.Lam (Nameless.Lam (Nameless.Var 0))
    , Nothing
    , Just (Nameless.Clos [] (Nameless.Lam (Nameless.Var 0)))
    )
  , ( "8. nested lambda - uses both variables"
    , Named.Anno
        (Named.Lam "x" (Named.Lam "y" (Named.App (Named.Var "x") (Named.Var "y"))))
        (Named.TyArr 
          (Named.TyArr (Named.TyLit Nameless.TyInt) (Named.TyLit Nameless.TyInt))
          (Named.TyArr (Named.TyLit Nameless.TyInt) (Named.TyLit Nameless.TyInt)))
    , Nameless.Anno
        (Nameless.Lam (Nameless.Lam (Nameless.App (Nameless.Var 1) (Nameless.Var 0))))
        (Nameless.TyArr 
          (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt))
          (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt)))
    , Just (Nameless.TyArr 
          (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt))
          (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt)))
    , Just (Nameless.Clos [] (Nameless.Lam (Nameless.App (Nameless.Var 1) (Nameless.Var 0))))
    )

    -- ==========================================================================
    -- Application (9-11)
    -- ==========================================================================
  , ( "9. simple application"
    , Named.App 
        (Named.Anno 
          (Named.Lam "x" (Named.Var "x"))
          (Named.TyArr (Named.TyLit Nameless.TyInt) (Named.TyLit Nameless.TyInt)))
        (Named.Lit (Nameless.LitInt 5))
    , Nameless.App 
        (Nameless.Anno 
          (Nameless.Lam (Nameless.Var 0))
          (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt)))
        (Nameless.Lit (Nameless.LitInt 5))
    , Just (Nameless.TyLit Nameless.TyInt)
    , Just (Nameless.Lit (Nameless.LitInt 5))
    )
  , ( "10. curried application"
    , Named.App 
        (Named.App 
          (Named.Anno 
            (Named.Lam "x" (Named.Lam "y" (Named.Var "x")))
            (Named.TyArr (Named.TyLit Nameless.TyInt) 
              (Named.TyArr (Named.TyLit Nameless.TyBool) (Named.TyLit Nameless.TyInt))))
          (Named.Lit (Nameless.LitInt 42)))
        (Named.Lit (Nameless.LitBool True))
    , Nameless.App 
        (Nameless.App 
          (Nameless.Anno 
            (Nameless.Lam (Nameless.Lam (Nameless.Var 1)))
            (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) 
              (Nameless.TyArr (Nameless.TyLit Nameless.TyBool) (Nameless.TyLit Nameless.TyInt))))
          (Nameless.Lit (Nameless.LitInt 42)))
        (Nameless.Lit (Nameless.LitBool True))
    , Just (Nameless.TyLit Nameless.TyInt)
    , Just (Nameless.Lit (Nameless.LitInt 42))
    )
  , ( "11. application returning second argument"
    , Named.App 
        (Named.App 
          (Named.Anno 
            (Named.Lam "x" (Named.Lam "y" (Named.Var "y")))
            (Named.TyArr (Named.TyLit Nameless.TyInt) 
              (Named.TyArr (Named.TyLit Nameless.TyBool) (Named.TyLit Nameless.TyBool))))
          (Named.Lit (Nameless.LitInt 42)))
        (Named.Lit (Nameless.LitBool False))
    , Nameless.App 
        (Nameless.App 
          (Nameless.Anno 
            (Nameless.Lam (Nameless.Lam (Nameless.Var 0)))
            (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) 
              (Nameless.TyArr (Nameless.TyLit Nameless.TyBool) (Nameless.TyLit Nameless.TyBool))))
          (Nameless.Lit (Nameless.LitInt 42)))
        (Nameless.Lit (Nameless.LitBool False))
    , Just (Nameless.TyLit Nameless.TyBool)
    , Just (Nameless.Lit (Nameless.LitBool False))
    )

    -- ==========================================================================
    -- Type Abstraction and Application (12-15)
    -- ==========================================================================
    -- Note: TLam containing Lam cannot be inferred, only checked
  , ( "12. polymorphic identity (annotated)"
    , Named.Anno
        (Named.TLam "a" (Named.Lam "x" (Named.Var "x")))
        (Named.TyAll "a" (Named.TyArr (Named.TyVar "a") (Named.TyVar "a")))
    , Nameless.Anno
        (Nameless.TLam (Nameless.Lam (Nameless.Var 0)))
        (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0)))
    , Just (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0)))
    , Just (Nameless.TClos [] (Nameless.Lam (Nameless.Var 0)))
    )
  , ( "13. type application of polymorphic identity (annotated)"
    , Named.TApp 
        (Named.Anno
          (Named.TLam "a" (Named.Lam "x" (Named.Var "x")))
          (Named.TyAll "a" (Named.TyArr (Named.TyVar "a") (Named.TyVar "a"))))
        (Named.TyLit Nameless.TyInt)
    , Nameless.TApp 
        (Nameless.Anno
          (Nameless.TLam (Nameless.Lam (Nameless.Var 0)))
          (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0))))
        (Nameless.TyLit Nameless.TyInt)
    , Just (Nameless.TySubstT (Nameless.TyLit Nameless.TyInt) 
            (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0)))
    , Just (Nameless.Clos [Nameless.TypE (Nameless.TyBoxT [] (Nameless.TyLit Nameless.TyInt))] 
            (Nameless.Var 0))
    )
  , ( "14. nested type abstraction (annotated)"
    , Named.Anno
        (Named.TLam "a" (Named.TLam "b" (Named.Lam "x" (Named.Var "x"))))
        (Named.TyAll "a" (Named.TyAll "b" (Named.TyArr (Named.TyVar "b") (Named.TyVar "b"))))
    , Nameless.Anno
        (Nameless.TLam (Nameless.TLam (Nameless.Lam (Nameless.Var 0))))
        (Nameless.TyAll (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0))))
    , Just (Nameless.TyAll (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0))))
    , Just (Nameless.TClos [] (Nameless.TLam (Nameless.Lam (Nameless.Var 0))))
    )
  , ( "15. type variable in type annotation"
    , Named.TLam "a" 
        (Named.Anno 
          (Named.Lam "x" (Named.Var "x"))
          (Named.TyArr (Named.TyVar "a") (Named.TyVar "a")))
    , Nameless.TLam 
        (Nameless.Anno 
          (Nameless.Lam (Nameless.Var 0))
          (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0)))
    , Just (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0)))
    , Just (Nameless.TClos [] 
        (Nameless.Anno 
          (Nameless.Lam (Nameless.Var 0))
          (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0))))
    )

    -- ==========================================================================
    -- Records (16-18)
    -- ==========================================================================
  , ( "16. simple record"
    , Named.Rec "x" (Named.Lit (Nameless.LitInt 42))
    , Nameless.Rec "x" (Nameless.Lit (Nameless.LitInt 42))
    , Just (Nameless.TyRcd "x" (Nameless.TyLit Nameless.TyInt))
    , Just (Nameless.Rec "x" (Nameless.Lit (Nameless.LitInt 42)))
    )
  , ( "17. record projection via FEnv"
    , Named.RProj 
        (Named.FEnv [Named.ExpE "x" (Named.Rec "val" (Named.Lit (Nameless.LitInt 42)))])
        "val"
    , Nameless.RProj 
        (Nameless.FEnv [Nameless.ExpE (Nameless.Rec "val" (Nameless.Lit (Nameless.LitInt 42)))])
        "val"
    , Just (Nameless.TyLit Nameless.TyInt)
    , Just (Nameless.Lit (Nameless.LitInt 42))
    )
  , ( "18. record with lambda"
    , Named.Rec "f" 
        (Named.Anno 
          (Named.Lam "x" (Named.Var "x"))
          (Named.TyArr (Named.TyLit Nameless.TyInt) (Named.TyLit Nameless.TyInt)))
    , Nameless.Rec "f" 
        (Nameless.Anno 
          (Nameless.Lam (Nameless.Var 0))
          (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt)))
    , Just (Nameless.TyRcd "f" 
        (Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyInt)))
    , Just (Nameless.Rec "f" (Nameless.Clos [] (Nameless.Var 0)))
    )

    -- ==========================================================================
    -- First-Class Environments - Basic (19-22)
    -- ==========================================================================
  , ( "19. empty environment"
    , Named.FEnv []
    , Nameless.FEnv []
    , Just (Nameless.TyEnvt [])
    , Just (Nameless.FEnv [])
    )
  , ( "20. environment with single ExpE"
    , Named.FEnv [Named.ExpE "x" (Named.Lit (Nameless.LitInt 42))]
    , Nameless.FEnv [Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))]
    , Just (Nameless.TyEnvt [Nameless.Type (Nameless.TyLit Nameless.TyInt)])
    , Just (Nameless.FEnv [Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))])
    )
  , ( "21. environment with multiple ExpE"
    , Named.FEnv 
        [ Named.ExpE "x" (Named.Lit (Nameless.LitInt 1))
        , Named.ExpE "y" (Named.Lit (Nameless.LitInt 2))
        ]
    , Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 1))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 2))
        ]
    , Just (Nameless.TyEnvt 
        [ Nameless.Type (Nameless.TyLit Nameless.TyInt)
        , Nameless.Type (Nameless.TyLit Nameless.TyInt)
        ])
    , Just (Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 1))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 2))
        ])
    )
  , ( "22. environment with TypE"
    , Named.FEnv [Named.TypE "t" (Named.TyLit Nameless.TyInt)]
    , Nameless.FEnv [Nameless.TypE (Nameless.TyLit Nameless.TyInt)]
    , Just (Nameless.TyEnvt [Nameless.TypeEq (Nameless.TyLit Nameless.TyInt)])
    , Just (Nameless.FEnv [Nameless.TypE (Nameless.TyBoxT [] (Nameless.TyLit Nameless.TyInt))])
    )

    -- ==========================================================================
    -- First-Class Environments - Scoping (23-26)
    -- ==========================================================================
  , ( "23. environment entry references later entry"
    , Named.FEnv 
        [ Named.ExpE "x" (Named.Var "y")
        , Named.ExpE "y" (Named.Lit (Nameless.LitInt 42))
        ]
    , Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Var 0)  -- x sees y at index 0
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))
        ]
    , Just (Nameless.TyEnvt 
        [ Nameless.Type (Nameless.TyLit Nameless.TyInt)
        , Nameless.Type (Nameless.TyLit Nameless.TyInt)
        ])
    , Just (Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))
        ])
    )
  , ( "24. environment with three entries, first references third"
    , Named.FEnv 
        [ Named.ExpE "x" (Named.Var "z")
        , Named.ExpE "y" (Named.Lit (Nameless.LitInt 1))
        , Named.ExpE "z" (Named.Lit (Nameless.LitInt 2))
        ]
    , Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Var 1)  -- x sees z at index 1 (y=0, z=1)
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 1))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 2))
        ]
    , Just (Nameless.TyEnvt 
        [ Nameless.Type (Nameless.TyLit Nameless.TyInt)
        , Nameless.Type (Nameless.TyLit Nameless.TyInt)
        , Nameless.Type (Nameless.TyLit Nameless.TyInt)
        ])
    , Just (Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 2))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 1))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 2))
        ])
    )
  , ( "25. environment with second references third"
    , Named.FEnv 
        [ Named.ExpE "x" (Named.Lit (Nameless.LitInt 0))
        , Named.ExpE "y" (Named.Var "z")
        , Named.ExpE "z" (Named.Lit (Nameless.LitInt 99))
        ]
    , Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 0))
        , Nameless.ExpE (Nameless.Var 0)  -- y sees z at index 0
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 99))
        ]
    , Just (Nameless.TyEnvt 
        [ Nameless.Type (Nameless.TyLit Nameless.TyInt)
        , Nameless.Type (Nameless.TyLit Nameless.TyInt)
        , Nameless.Type (Nameless.TyLit Nameless.TyInt)
        ])
    , Just (Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 0))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 99))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 99))
        ])
    )
  , ( "26. environment with mixed ExpE and TypE"
    , Named.FEnv 
        [ Named.ExpE "x" (Named.Lit (Nameless.LitInt 1))
        , Named.TypE "t" (Named.TyLit Nameless.TyBool)
        , Named.ExpE "y" (Named.Lit (Nameless.LitInt 2))
        ]
    , Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 1))
        , Nameless.TypE (Nameless.TyLit Nameless.TyBool)
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 2))
        ]
    , Just (Nameless.TyEnvt 
        [ Nameless.Type (Nameless.TyLit Nameless.TyInt)
        , Nameless.TypeEq (Nameless.TyLit Nameless.TyBool)
        , Nameless.Type (Nameless.TyLit Nameless.TyInt)
        ])
    -- Eval result: TypE gets wrapped in TyBoxT with c2g of (rest ++ env)
    -- For the TypE at position 1, c2g of [ExpE (Lit 2)] ++ [] = []
    , Just (Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 1))
        , Nameless.TypE (Nameless.TyBoxT [] (Nameless.TyLit Nameless.TyBool))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 2))
        ])
    )

    -- ==========================================================================
    -- ModE and MVar (27-29)
    -- ==========================================================================
  , ( "27. ModE wraps in FEnv containing record"
    , Named.FEnv [Named.ModE "m" (Named.Lit (Nameless.LitInt 42))]
    , Nameless.FEnv [Nameless.ExpE (Nameless.Rec "m" (Nameless.Lit (Nameless.LitInt 42)))]
    , Just (Nameless.TyEnvt [Nameless.Type (Nameless.TyRcd "m" (Nameless.TyLit Nameless.TyInt))])
    , Just (Nameless.FEnv [Nameless.ExpE (Nameless.Rec "m" (Nameless.Lit (Nameless.LitInt 42)))])
    )
  , ( "28. ModE projection via RProj on FEnv"
    -- To project from ModE, we need to go through FEnv and RProj
    , Named.RProj 
        (Named.FEnv [Named.ModE "m" (Named.Lit (Nameless.LitInt 42))])
        "m"
    , Nameless.RProj 
        (Nameless.FEnv [Nameless.ExpE (Nameless.Rec "m" (Nameless.Lit (Nameless.LitInt 42)))])
        "m"
    , Just (Nameless.TyLit Nameless.TyInt)
    , Just (Nameless.Lit (Nameless.LitInt 42))
    )
  , ( "29. Var referencing ExpE stays as Var"
    , Named.FEnv 
        [ Named.ExpE "result" (Named.Var "x")  -- x is ExpE, stays as Var
        , Named.ExpE "x" (Named.Lit (Nameless.LitInt 42))
        ]
    , Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Var 0)
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))
        ]
    , Just (Nameless.TyEnvt 
        [ Nameless.Type (Nameless.TyLit Nameless.TyInt)
        , Nameless.Type (Nameless.TyLit Nameless.TyInt)
        ])
    , Just (Nameless.FEnv 
        [ Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))
        , Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))
        ])
    )

    -- ==========================================================================
    -- Box and Closures (30-32)
    -- ==========================================================================
  , ( "30. box with simple environment"
    , Named.Box 
        [Named.ExpE "x" (Named.Lit (Nameless.LitInt 42))]
        (Named.Var "x")
    , Nameless.Box 
        [Nameless.ExpE (Nameless.Lit (Nameless.LitInt 42))]
        (Nameless.Var 0)
    , Just (Nameless.TyBoxT 
        [Nameless.Type (Nameless.TyLit Nameless.TyInt)]
        (Nameless.TyLit Nameless.TyInt))
    , Just (Nameless.Lit (Nameless.LitInt 42))
    )
  , ( "31. closure with environment"
    , Named.Clos 
        [Named.ExpE "captured" (Named.Lit (Nameless.LitInt 10))]
        (Named.Var "captured")
    , Nameless.Clos 
        [Nameless.ExpE (Nameless.Lit (Nameless.LitInt 10))]
        (Nameless.Var 0)
    , Nothing  -- closures need checking, not inference
    , Just (Nameless.Clos 
        [Nameless.ExpE (Nameless.Lit (Nameless.LitInt 10))]
        (Nameless.Var 0))
    )
  , ( "32. tclos with type environment"
    , Named.TClos 
        [Named.TypE "t" (Named.TyLit Nameless.TyInt)]
        (Named.Lam "x" (Named.Var "x"))
    , Nameless.TClos 
        [Nameless.TypE (Nameless.TyLit Nameless.TyInt)]
        (Nameless.Lam (Nameless.Var 0))
    , Nothing  -- closures need checking
    , Just (Nameless.TClos 
        [Nameless.TypE (Nameless.TyLit Nameless.TyInt)]
        (Nameless.Lam (Nameless.Var 0)))
    )

    -- ==========================================================================
    -- Complex Type Translations (33-35)
    -- ==========================================================================
  , ( "33. forall type in annotation"
    , Named.Anno 
        (Named.TLam "a" (Named.Lam "x" (Named.Var "x")))
        (Named.TyAll "a" (Named.TyArr (Named.TyVar "a") (Named.TyVar "a")))
    , Nameless.Anno 
        (Nameless.TLam (Nameless.Lam (Nameless.Var 0)))
        (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0)))
    , Just (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0)))
    , Just (Nameless.TClos [] (Nameless.Lam (Nameless.Var 0)))
    )
  , ( "34. nested forall types"
    , Named.Anno 
        (Named.TLam "a" (Named.TLam "b" (Named.Lam "x" (Named.Var "x"))))
        (Named.TyAll "a" (Named.TyAll "b" (Named.TyArr (Named.TyVar "b") (Named.TyVar "b"))))
    , Nameless.Anno 
        (Nameless.TLam (Nameless.TLam (Nameless.Lam (Nameless.Var 0))))
        (Nameless.TyAll (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0))))
    , Just (Nameless.TyAll (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 0) (Nameless.TyVar 0))))
    , Just (Nameless.TClos [] (Nameless.TLam (Nameless.Lam (Nameless.Var 0))))
    )
  , ( "35. forall referencing outer type variable"
    , Named.Anno 
        (Named.TLam "a" (Named.TLam "b" (Named.Lam "x" (Named.Var "x"))))
        (Named.TyAll "a" (Named.TyAll "b" (Named.TyArr (Named.TyVar "a") (Named.TyVar "a"))))
    , Nameless.Anno 
        (Nameless.TLam (Nameless.TLam (Nameless.Lam (Nameless.Var 0))))
        (Nameless.TyAll (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 1) (Nameless.TyVar 1))))
    , Just (Nameless.TyAll (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 1) (Nameless.TyVar 1))))
    , Just (Nameless.TClos [] (Nameless.TLam (Nameless.Lam (Nameless.Var 0))))
    )
  ]

-- ============================================================================
-- Type-only tests
-- ============================================================================

typeDebruijnTests :: [(String, Named.Typ, Nameless.Typ)]
typeDebruijnTests =
  [ ( "type: simple literal"
    , Named.TyLit Nameless.TyInt
    , Nameless.TyLit Nameless.TyInt
    )
  , ( "type: arrow"
    , Named.TyArr (Named.TyLit Nameless.TyInt) (Named.TyLit Nameless.TyBool)
    , Nameless.TyArr (Nameless.TyLit Nameless.TyInt) (Nameless.TyLit Nameless.TyBool)
    )
  , ( "type: forall with variable"
    , Named.TyAll "a" (Named.TyVar "a")
    , Nameless.TyAll (Nameless.TyVar 0)
    )
  , ( "type: nested forall"
    , Named.TyAll "a" (Named.TyAll "b" (Named.TyArr (Named.TyVar "a") (Named.TyVar "b")))
    , Nameless.TyAll (Nameless.TyAll (Nameless.TyArr (Nameless.TyVar 1) (Nameless.TyVar 0)))
    )
  , ( "type: record type"
    , Named.TyRcd "label" (Named.TyLit Nameless.TyInt)
    , Nameless.TyRcd "label" (Nameless.TyLit Nameless.TyInt)
    )
  ]
-- ============================================================================
-- Spec
-- ============================================================================

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
              eval [] (toDeBruijn namedExp) `shouldBe` Just result
          Nothing ->
            it "evaluation not expected (skipped)" $
              True `shouldBe` True  -- trivial assertion
    
    mkTypeTest (name, namedTyp, expectedNameless) =
      it name $
        toDeBruijnTyp namedTyp `shouldBe` expectedNameless