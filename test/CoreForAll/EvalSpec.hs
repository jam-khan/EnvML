module CoreForAll.EvalSpec (spec) where

import CoreForAll.Eval (eval)
import CoreForAll.Syntax
import Test.Hspec

eval0 :: Exp -> Maybe Exp
eval0 = eval []

--
-- var0 :: Exp
-- var0 = Var 0
--
idE :: Exp
idE = Lam (Var 0)

lit :: Int -> Exp
lit n = Lit (LitInt n)

constFun :: Exp
constFun = Lam (Lam (Var 1))

selfApp :: Exp
selfApp = Lam (App (Var 0) (Var 0))

-- idApp42 :: Exp
-- idApp42 = App idE (Lit 42)
--
-- tid :: Exp
-- tid = TLam (Lam (Var 0))
--
-- tidApp42 :: Exp
-- tidApp42 = App (TApp tid TyInt) (Lit 42)
--
-- recX42 :: Exp
-- recX42 = Rec "x" (Lit 42)
--
-- projX42 :: Exp
-- projX42 = RProj recX42 "x"
--
fixId :: Exp
fixId = Fix idE

fixE :: Exp -> Exp
fixE = Fix

zero :: Exp
zero = Lam (Lam (Var 0))

one :: Exp
one = Lam (Lam (App (Var 1) (Var 0)))

succ :: Exp
succ = Lam (Lam (Lam (App (Var 1) (App (App (Var 2) (Var 1)) (Var 0)))))

add :: Exp
add = Fix ()

evalTests :: [(String, Exp, Maybe Exp)]
evalTests =
  [ ( "literal",
      Lit (LitInt 42),
      Just (Lit (LitInt 42))
    ),
    ( "fix produces a closure",
      fixId,
      Just (Clos [] (Fix idE))
    ),
    ( "recursive record lookup",
      recLookup (Rec "a" (Rec "a" (Rec "a" (Lit (LitInt 100))))),
      Just (Lit (LitInt 100))
    )
  ]

spec :: Spec
spec =
  describe "CoreForAll.Eval.eval" $
    mapM_ mkTest evalTests
  where
    mkTest (name, e, expected) =
      it name $
        eval0 e `shouldBe` expected
