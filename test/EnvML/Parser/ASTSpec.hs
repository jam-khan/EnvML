module EnvML.Parser.ASTSpec (spec) where

import EnvML.Parser.AST
import EnvML.Parser.Pretty

import Test.Hspec

spec :: Spec
spec = do
  describe "prettyExp" $ do
    mapM_ mkExpTest prettyExpTests

  describe "prettyTyp" $ do
    mapM_ mkTypTest prettyTypTests

mkExpTest :: (Exp, String) -> SpecWith ()
mkExpTest (input, expected) =
  it ("pretty prints " ++ show input) $ do
    let actual = prettyExp input
    actual `shouldBe` expected

mkTypTest :: (Typ, String) -> SpecWith ()
mkTypTest (input, expected) =
  it ("pretty prints " ++ show input) $ do
    let actual = prettyTyp input
    actual `shouldBe` expected

int :: Typ
int = TyLit TyInt

x, y, z :: Exp
x = Var "x"
y = Var "y"
z = Var "z"

prettyExpTests :: [(Exp, String)]
prettyExpTests =
  [ (Lit (LitInt 0), "0")
  , (Lit (LitInt 42), "42")
  , (Var "x", "x")
  , (App x y, "x(y)")
  , (App (App x y) z, "x(y)(z)")
  , (App x (App y z), "x(y(z))")
  , (Lam [("x", TmArg)] x, "fun (x) -> x")
  , (Lam [("x", TmArg)] (App x y), "fun (x) -> x(y)")
  , (App (Lam [("x", TmArg)] x) y, "(fun (x) -> x)(y)")
  , (Lam [("a", TyArg)] x, "fun (a : Type) -> x")
  , (Lam [("x", TmArg)] (Lam [("a", TyArg)] x), "fun (x) -> fun (a : Type) -> x")
  , (TApp x int, "x<int>")
  , (TApp (App x y) int, "x(y)<int>")
  , (App (TApp x int) y, "x<int>(y)")
  , (Anno x int, "x :: int")
  , (Anno (App x y) int, "x(y) :: int")
  , (App (Anno x int) y, "(x :: int)(y)")
  , (Box [] x, "box [] in x")
  , (Box [] (App x y), "box [] in x(y)")
  , (App (Box [] x) y, "(box [] in x)(y)")
  , (Clos [] "x" x, "clos [] (x) -> x")
  , (App (Clos [] "x" x) y, "(clos [] (x) -> x)(y)")
  , (Clos [("x", ExpE x)] "y" (App x y), "clos [x = x] (y) -> x(y)")
  , (Rec "x" (Lit (LitInt 42)), "{x = 42}")
  , (RProj x "x", "x.x")
  , (RProj (App x y) "x", "x(y).x")
  , (FEnv [], "[]")
  , (FEnv [("x", ExpE x)], "[x = x]")
  , (FEnv [("t", TypE int), ("x", ExpE (Lit (LitInt 42)))], "[type t = int, x = 42]")
  ]

prettyTypTests :: [(Typ, String)]
prettyTypTests =
  [ (int, "int")
  , (TyVar "x", "x")
  , (TyArr int int, "(int -> int)")
  , (TyArr int (TyArr int int), "(int -> (int -> int))")
  , (TyArr (TyArr int int) int, "((int -> int) -> int)")
  , (TyAll "a" a, "forall a. a")
  , (TyAll "a" (TyArr a a), "forall a. (a -> a)")
  , (TyRcd "x" int, "{x : int}")
  , (TyEnvt [("x", Type int)], "[x : int]")
  , (TyBoxT [] int, "[] ===> int")
  , (TyModule (TySig []), "sig  end")
  ]
  where
    a = TyVar "a"
