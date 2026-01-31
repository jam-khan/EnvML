module Core.EvalSpec (spec) where

--
import Core.Eval (eval)
import Core.Syntax
import Test.Hspec

eval0 :: Exp -> Maybe Exp
eval0 = eval []

evalTests :: [(String, Exp, Maybe Exp)]
evalTests =
  [ ( "int literal evaluates to itself",
      Lit (LitInt 42),
      Just (Lit (LitInt 42))
    ),
    ( "sub operation evaluates correctly",
      BinOp $ Sub (Lit (LitInt 5)) (Lit (LitInt 3)),
      Just (Lit (LitInt 2))
    ),
    ( "mul operation evaluates correctly",
      BinOp $ Mul (Lit (LitInt 4)) (Lit (LitInt 2)),
      Just (Lit (LitInt 8))
    ),
    ( "if expression evaluates correctly",
      If (Lit (LitBool True)) (Lit (LitInt 1)) (Lit (LitInt 0)),
      Just (Lit (LitInt 1))
    ),
    ( "equality evaluates correctly",
      BinOp $ EqEq (Lit (LitInt 1)) (Lit (LitInt 2)),
      Just (Lit (LitBool False))
    ),
    ( "function application",
      App
        (Lam (BinOp $ Sub (Var 0) (Lit (LitInt 1))))
        (Lit (LitInt 5)),
      Just (Lit (LitInt 4))
    ),
    ( "empty closure application",
      App
        ( Clos
            []
            (BinOp $ Sub (Var 0) (Lit (LitInt 1)))
        )
        (Lit (LitInt 10)),
      Just (Lit (LitInt 9))
    ),
    ( "closure application with env",
      App
        ( Clos
            [ExpE (Lit (LitInt 3))]
            (BinOp $ Mul (Var 0) (Var 1))
        )
        (Lit (LitInt 10)),
      Just (Lit (LitInt 30))
    ),
    ( "first-class environments",
      FEnv [ExpE (Lit (LitInt 3)), TypE (TyLit TyInt), ExpE (Lit (LitBool True)), TypE (TyLit TyBool)],
      Just (FEnv [ExpE (Lit (LitInt 3)), TypE (TyBoxT [TypeEq (TyBoxT [] (TyLit TyBool))] (TyLit TyInt)), ExpE (Lit (LitBool True)), TypE (TyBoxT [] (TyLit TyBool))])
    ),
    ( "fixpoint factorial",
      let factorial =
            Fix
              ( Lam
                  ( If
                      (BinOp $ EqEq (Var 0) (Lit (LitInt 0)))
                      (Lit (LitInt 1))
                      ( BinOp $ Mul
                          (Var 0)
                          (App (Var 1) (BinOp $ Sub (Var 0) (Lit (LitInt 1))))
                      )
                  )
              )
       in App factorial (Lit (LitInt 5)),
      Just (Lit (LitInt 120))
    ),
    ( "fixpoint factorial correctly refers to outside variable",
      let factorial =
            Fix
              ( Lam
                  ( If
                      (BinOp $ EqEq (Var 0) (Lit (LitInt 0)))
                      (Var 2)
                      ( BinOp $ Mul
                          (Var 0)
                          (App (Var 1) (BinOp $ Sub (Var 0) (Lit (LitInt 1))))
                      )
                  )
              )
       in App (Lam (App factorial (Lit (LitInt 5)))) (Lit (LitInt 1)),
      Just (Lit (LitInt 120))
    )
  ]

spec :: Spec
spec =
  describe "Core.Eval.eval" $
    mapM_ mkTest evalTests
  where
    mkTest (name, e, expected) =
      it name $
        eval [] e `shouldBe` expected
