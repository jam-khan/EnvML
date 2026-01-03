module EnvML.PrintTypSpec (spec) where

import Test.Hspec
import EnvML.Syntax
import EnvML.Print (stringOfTyp)

-- Shorthands
int :: Typ
int = TyLit TyInt

a, b, c :: Typ
a = TyVar "a"
b = TyVar "b"
c = TyVar "c"

prettyTypTests :: [(Typ, String)]
prettyTypTests =
  [ -- Base types
    (int, "int")
  , (TyVar "x", "x")

    -- Arrow types
  , (TyArr int int, "int -> int")
  , (TyArr a b, "a -> b")
  , (TyArr int (TyArr int int), "int -> int -> int")
  , (TyArr (TyArr int int) int, "(int -> int) -> int")
  , (TyArr a (TyArr b c),
      "a -> b -> c")
  , (TyArr (TyArr a b) c,
      "(a -> b) -> c")

    -- Forall types
  , (TyAll "a" a,
      "forall a. a")
  , (TyAll "a" (TyArr a a),
      "forall a. a -> a")
  , (TyAll "a" (TyAll "b" (TyArr a b)),
      "forall a. forall b. a -> b")
  , (TyArr (TyAll "a" a) int,
      "(forall a. a) -> int")
  , (TyAll "a" (TyArr int a),
      "forall a. int -> a")

    -- Record types
  , (TyRcd "x" int,
      "{x : int}")
  , (TyRcd "f" (TyArr int int),
      "{f : int -> int}")
  , (TyRcd "r" (TyAll "a" a),
      "{r : forall a. a}")

    -- Environment types
  , (TyEnvt [],
      "[]")
  , (TyEnvt [("x", Type int)],
      "[x : int]")
  , (TyEnvt [("A", Kind)],
      "[A : Type]")
  , (TyEnvt [("T", TypeEq a)],
      "[T = a]")
  , (TyEnvt [("x", Type int), ("y", Type a)],
      "[x : int, y : a]")
  , (TyEnvt [("A", Kind), ("T", TypeEq b), ("x", Type int)],
      "[A : Type, T = b, x : int]")

    -- Box types
  , (TyBoxT [] int,
      "[] ===> int")
  , (TyBoxT [("x", Type int)] a,
      "[x : int] ===> a")
  , (TyBoxT [("x", Type int), ("y", Type b)] c,
      "[x : int, y : b] ===> c")
  , (TyArr (TyBoxT [] int) int,
      "([] ===> int) -> int")
  , (TyBoxT [] (TyArr int int),
      "[] ===> int -> int")

    -- Substitution types
  , (TySubstT a "x" int,
      "a[x:=int]")
  , (TySubstT a "x" (TyArr int int),
      "a[x:=(int -> int)]")

  , (TySubstT a "x" (TySubstT b "y" int),
      "a[x:=b[y:=int]]")

  , (TyArr (TySubstT a "x" int) b,
      "a[x:=int] -> b")
  , (TySubstT a "x" (TyArr b c),
      "a[x:=(b -> c)]")

  , (TyAll "a" (TySubstT b "x" a),
      "forall a. b[x:=a]")

  , (TyBoxT [] (TySubstT a "x" int),
      "[] ===> a[x:=int]")

    -- Module types
  , (TyModule (TySig []),
      "sig  end")
  , (TyModule (TySig [TyDef "t" int]),
      "sig type t = int end")
  , (TyModule (TyArrowM int (TySig [])),
      "(int ->m sig  end)")
  , (TyModule (TyArrowM (TyArr int int) (TySig [])),
      "(int -> int ->m sig  end)")
  , (TyArr int (TyModule (TyArrowM int (TySig []))), 
      "int -> (int ->m sig  end)")
  ]

spec :: Spec
spec =
  describe "Pretty.stringOfTyp" $
    mapM_ mkTest prettyTypTests
  where
    mkTest (t, expected) =
      it ("prints " ++ stringOfTyp t) $
        stringOfTyp t `shouldBe` expected
