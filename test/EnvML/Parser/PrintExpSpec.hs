module EnvML.Parser.PrintExpSpec (spec) where

import Test.Hspec
import EnvML.Parser.AST
import EnvML.Print (stringOfExp)

-- Shorthands
int :: Typ
int = TyLit TyInt

x, y, z :: Exp
x = Var "x"
y = Var "y"
z = Var "z"

prettyExpTests :: [(Exp, String)]
prettyExpTests =
  [ -- Literals
    (Lit (LitInt 0),  "0")
  , (Lit (LitInt 42), "42")

    -- Variables
  , (Var "x", "x")

    -- Application
  , (App x y, "x(y)")
  , (App (App x y) z, "x(y)(z)")
  , (App x (App y z), "x(y(z))")

    -- Lambdas
  , (Lam "x" int x, "fun (x: int) -> x")
  , (Lam "x" int (App x y), "fun (x: int) -> x(y)")
  , (App (Lam "x" int x) y, "(fun (x: int) -> x)(y)")

    -- Type abstraction
  , (TLam "a" x, "fun type a -> x")
  , (Lam "x" (TyVar "a") (TLam "a" x),
      "fun (x: a) -> fun type a -> x")

    -- Type application
  , (TApp x int, "x<int>")
  , (TApp (App x y) int, "x(y)<int>")
  , (App (TApp x int) y, "x<int>(y)")

    -- Annotations
  , (Anno x int, "x :: int")
  , (Anno (App x y) int, "x(y) :: int")
  , (App (Anno x int) y, "(x :: int)(y)")

    -- Boxes
  , (Box [] x, "box [] in x")
  , (Box [] (App x y), "box [] in x(y)")
  , (App (Box [] x) y, "(box [] in x)(y)")

    -- Closures
  , (Clos [] "x" int x, "clos [] (x: int) -> x")
  , (App (Clos [] "x" int x) y, "(clos [] (x: int) -> x)(y)")
  , (Clos [("x", ExpE x)] "y" int (App x y),
      "clos [x = x] (y: int) -> x(y)")

    -- Records
  , (Rec "x" (Lit (LitInt 42)), "{x = 42}")
  , (RProj x "x", "x.x")
  , (RProj (App x y) "x", "x(y).x")

    -- Environments
  , (FEnv [], "[]")
  , (FEnv [("x", ExpE x)], "[x = x]")
  , (FEnv [("t", TypE int), ("x", ExpE (Lit (LitInt 42)))],
      "[type t = int, x = 42]")

    -- Precedence tests
  , (App (RProj x "x") y, "x.x(y)")
  , (Anno (RProj x "x") int, "x.x :: int")

    -- Module expressions
  , (ModE (Struct []),
     "struct  end")

  , (ModE (Struct [("x", ExpE (Lit (LitInt 1)))]),
     "struct x = 1 end")

  , (ModE (Functor "X" (TyVar "A") (Struct [])),
     "functor (X : A) struct  end")

  , (ModE
        (MApp
          (Functor "X" (TyVar "A") (Struct []))
          (Struct [])),
     "(functor (X : A) struct  end) (struct  end)")

  , (ModE
        (MLink
          (Struct [])
          (Struct [])),
     "(struct  end) |><| (struct  end)")

  , (RProj (ModE (Struct [])) "x",
     "struct  end.x")

  , (Anno (ModE (Struct [])) (TyModule (TySig [])),
     "struct  end :: sig  end")

    -- Precedence tests
  , (App (Lam "x" int x) (Lam "y" int y),
     "(fun (x: int) -> x)(fun (y: int) -> y)")

  , (App (Box [] (Lam "x" int x)) y,
     "(box [] in fun (x: int) -> x)(y)")

  , (RProj (TApp x (TyVar "A")) "l",
     "x<A>.l")

  , (Anno (App (TApp x int) y) int,
     "x<int>(y) :: int")

  , (App (Anno x int) (Anno y int),
     "(x :: int)(y :: int)")
  ]

spec :: Spec
spec =
  describe "Pretty.stringOfExp" $
    mapM_ mkTest prettyExpTests
  where
    mkTest (e, expected) =
      it ("prints " ++ stringOfExp e) $
        stringOfExp e `shouldBe` expected
