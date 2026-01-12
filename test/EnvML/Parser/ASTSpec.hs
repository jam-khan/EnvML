module EnvML.Parser.ASTSpec (spec) where

import Test.Hspec
import EnvML.Parser.AST

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
  , (TyArr int int, "(int -> int)")
  , (TyArr a b, "(a -> b)")
  , (TyArr int (TyArr int int), "(int -> (int -> int))")
  , (TyArr (TyArr int int) int, "((int -> int) -> int)")
  , (TyArr a (TyArr b c),
      "(a -> (b -> c))")
  , (TyArr (TyArr a b) c,
      "((a -> b) -> c)")

    -- Forall types
  , (TyAll "a" a,
      "forall a. a")
  , (TyAll "a" (TyArr a a),
      "forall a. (a -> a)")
  , (TyAll "a" (TyAll "b" (TyArr a b)),
      "forall a. forall b. (a -> b)")
  , (TyArr (TyAll "a" a) int,
      "((forall a. a) -> int)")
  , (TyAll "a" (TyArr int a),
      "forall a. (int -> a)")

    -- Record types
  , (TyRcd "x" int,
      "{x : int}")
  , (TyRcd "f" (TyArr int int),
      "{f : (int -> int)}")
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
      "(([] ===> int) -> int)")
  , (TyBoxT [] (TyArr int int),
      "[] ===> (int -> int)")

    -- Substitution types
  , (TySubstT "x" int a,
      "[x:=int]a")
  , (TySubstT "x" (TyArr int int) a,
      "[x:=(int -> int)]a")

  , (TySubstT "x" (TySubstT "y" int b) a,
      "[x:=[y:=int]b]a")

  , (TyArr (TySubstT "x" int a) b,
      "([x:=int]a -> b)")
  , (TySubstT "x" a (TyArr b c),
      "[x:=a]((b -> c))")

  , (TyAll "a" (TySubstT "x" b a),
      "forall a. [x:=b]a")

  , (TyBoxT [] (TySubstT "x" int a),
      "[] ===> [x:=int]a")

    -- Module types
  , (TyModule (TySig []),
      "sig  end")
  , (TyModule (TySig [TyDef "t" int]),
      "sig type t = int end")
  , (TyModule (TyArrowM int (TySig [])),
      "(int ->m sig  end)")
  , (TyModule (TyArrowM (TyArr int int) (TySig [])),
      "((int -> int) ->m sig  end)")
  , (TyArr int (TyModule (TyArrowM int (TySig []))), 
      "(int -> (int ->m sig  end))")
  ]

spec :: Spec
spec = do
  describe "Pretty.show" $
    mapM_ mkTest prettyExpTests
  describe "Pretty.show" $
    mapM_ mkTest prettyTypTests
  where
    mkTest (x, expected) =
      it ("prints " ++ show x) $
        show x `shouldBe` expected
