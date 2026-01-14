module CoreForAll.CheckSpec (spec) where

import CoreForAll.Check
import CoreForAll.Syntax
import Test.Hspec

typeCheckTests :: [(String, Exp, Typ)]
typeCheckTests =
  [ ( "int literal has type int",
      Lit (LitInt 42),
      TyLit TyInt
    ),
    ( "sub operation produces int",
      Sub (Lit (LitInt 5)) (Lit (LitInt 3)),
      TyLit TyInt
    ),
    ( "mul operation produces int",
      Mul (Lit (LitInt 4)) (Lit (LitInt 2)),
      TyLit TyInt
    ),
    ( "if expression with int branches",
      If (Lit (LitBool True)) (Lit (LitInt 1)) (Lit (LitInt 0)),
      TyLit TyInt
    ),
    ( "equality produces bool",
      Eq (Lit (LitInt 1)) (Lit (LitInt 2)),
      TyLit TyBool
    ),
    ( "int -> int function has correct type",
      Lam (Sub (Var 0) (Lit (LitInt 1))),
      TyArr (TyLit TyInt) (TyLit TyInt)
    ),
    ( "int -> int application returns int",
      App
        (Anno (Lam (Sub (Var 0) (Lit (LitInt 1)))) (TyArr (TyLit TyInt) (TyLit TyInt)))
        (Lit (LitInt 5)),
      TyLit TyInt
    ),
    ( "fixpoint function has correct type (factorial)",
      let factorial =
            Fix
              ( Lam
                  ( If
                      (Eq (Var 0) (Lit (LitInt 0)))
                      (Lit (LitInt 1))
                      ( Mul
                          (Var 0)
                          (App (Var 1) (Sub (Var 0) (Lit (LitInt 1))))
                      )
                  )
              )
       in App (Anno factorial (TyArr (TyLit TyInt) (TyLit TyInt))) (Lit (LitInt 5)),
      TyLit TyInt
    ),
    ( "fixpoint function has correct type (factorial)",
      let factorial =
            Fix
              ( Lam
                  ( If
                      (Eq (Var 0) (Lit (LitInt 0)))
                      (Lit (LitInt 1))
                      ( Mul
                          (Var 0)
                          (App (Var 1) (Sub (Var 0) (Lit (LitInt 1))))
                      )
                  )
              )
       in App (Anno factorial (TyArr (TyLit TyInt) (TyLit TyInt))) (Lit (LitInt 5)),
      TyLit TyInt
    ),
    ( "fixpoint function has correct type referring to outside variable (factorial)",
      let factorial =
            Fix
              ( Lam
                  ( If
                      (Eq (Var 0) (Lit (LitInt 0)))
                      (Var 2)
                      ( Mul
                          (Var 0)
                          (App (Var 1) (Sub (Var 0) (Lit (LitInt 1))))
                      )
                  )
              )
       in App (Anno (Lam (App (Anno factorial (TyArr (TyLit TyInt) (TyLit TyInt))) (Lit (LitInt 5)))) (TyArr (TyLit TyInt) (TyLit TyInt))) (Lit (LitInt 1)),
      TyLit TyInt
    )
  ]

spec :: Spec
spec =
  describe "CoreForAll.Check.check" $
    mapM_ mkTest typeCheckTests
  where
    mkTest (name, e, t) =
      it name $
        check [] e t `shouldBe` True
