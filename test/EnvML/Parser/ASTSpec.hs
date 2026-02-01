module EnvML.Parser.ASTSpec (spec) where

import EnvML.Parser.AST
import Test.Hspec

spec :: Spec
spec = do
  describe "prettyExp" $ do
    mapM_ mkExpTest prettyExpTests

  describe "prettyTyp" $ do
    mapM_ mkTypTest prettyTypTests

  describe "prettyModule" $ do
    mapM_ mkModuleTest prettyModuleTests

  describe "prettyTyCtxE" $ do
    mapM_ mkTyCtxTest prettyTyCtxTests

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

mkModuleTest :: (Module, String) -> SpecWith ()
mkModuleTest (input, expected) =
  it ("pretty prints module " ++ show input) $ do
    let actual = prettyModule input
    actual `shouldBe` expected

mkTyCtxTest :: (TyCtxE, String) -> SpecWith ()
mkTyCtxTest (input, expected) =
  it ("pretty prints TyCtxE " ++ show input) $ do
    let actual = prettyTyCtxE input
    actual `shouldBe` expected

int :: Typ
int = TyLit TyInt

bool :: Typ
bool = TyLit TyBool

x, y, z :: Exp
x = Var "x"
y = Var "y"
z = Var "z"

prettyExpTests :: [(Exp, String)]
prettyExpTests =
  -- Literals
  [ (Lit (LitInt 0), "0")
  , (Lit (LitInt 42), "42")
  , (Lit (LitBool True), "true")
  , (Lit (LitBool False), "false")
  , (Lit (LitStr "hello"), "\"hello\"")
  
  -- Variables
  , (Var "x", "x")
  
  -- Application
  , (App x y, "x(y)")
  , (App (App x y) z, "x(y)(z)")
  , (App x (App y z), "x(y(z))")
  
  -- Lambda - single arg
  , (Lam [("x", TmArg)] x, "fun (x) -> x")
  , (Lam [("x", TmArg)] (App x y), "fun (x) -> x(y)")
  , (App (Lam [("x", TmArg)] x) y, "(fun (x) -> x)(y)")
  
  -- Lambda - with type
  , (Lam [("x", TmArgType int)] x, "fun (x : int) -> x")
  
  -- Lambda - type argument
  , (Lam [("a", TyArg)] x, "fun (type a) -> x")
  , (Lam [("x", TmArg), ("a", TyArg)] x, "fun (x) (type a) -> x")
  
  -- Type application
  , (TApp x int, "x<int>")
  , (TApp (App x y) int, "x(y)<int>")
  , (App (TApp x int) y, "x<int>(y)")
  
  -- Annotation
  , (Anno x int, "x :: int")
  , (Anno (App x y) int, "x(y) :: int")
  , (App (Anno x int) y, "(x :: int)(y)")
  
  -- Box
  , (Box [] x, "box [] in x")
  , (Box [] (App x y), "box [] in x(y)")
  , (App (Box [] x) y, "(box [] in x)(y)")
  , (Box [ExpEN "x" x] y, "box [x = x] in y")
  , (Box [TypEN "t" int, ExpEN "x" (Lit (LitInt 42))] y, "box [type t = int, x = 42] in y")
  
  -- Clos - updated for FunArgs
  , (Clos [] [("x", TmArg)] x, "clos [] (x) -> x")
  , (App (Clos [] [("x", TmArg)] x) y, "(clos [] (x) -> x)(y)")
  , (Clos [ExpEN "x" x] [("y", TmArg)] (App x y), "clos [x = x] (y) -> x(y)")
  , (Clos [ExpEN "x" x] [("y", TmArgType int)] (App x y), "clos [x = x] (y : int) -> x(y)")
  
  -- Records - updated for [(Name, Exp)]
  , (Rec [("x", Lit (LitInt 42))], "{x = 42}")
  , (Rec [("x", x), ("y", y)], "{x = x, y = y}")
  , (Rec [], "{}")
  
  -- Record projection
  , (RProj x "x", "x.x")
  , (RProj (App x y) "x", "x(y).x")
  
  -- First-class environment
  , (FEnv [], "[]")
  , (FEnv [ExpEN "x" x], "[x = x]")
  , (FEnv [TypEN "t" int, ExpEN "x" (Lit (LitInt 42))], "[type t = int, x = 42]")
  , (FEnv [ExpE x], "[x]")
  , (FEnv [TypE int], "[int]")
  
  -- BinOp
  , (BinOp (Add x y), "x + y")
  , (BinOp (Sub x y), "x - y")
  , (BinOp (Mul x y), "x * y")
  , (BinOp (Add (BinOp (Add x y)) z), "x + y + z")
  
  -- Modules
  , (Mod (VarM "M"), "M")
  , (Mod (Struct [] []), "struct  end")
  , (Mod (Struct [] [ExpEN "x" x]), "struct x = x end")
  ]

prettyTypTests :: [(Typ, String)]
prettyTypTests =
  -- Base types
  [ (int, "int")
  , (bool, "bool")
  , (TyLit TyStr, "string")
  , (TyVar "x", "x")
  
  -- Arrows
  , (TyArr int int, "int -> int")
  , (TyArr int (TyArr int int), "int -> int -> int")
  , (TyArr (TyArr int int) int, "int -> int -> int")
  
  -- Forall
  , (TyAll "a" a, "forall a. a")
  , (TyAll "a" (TyArr a a), "forall a. a -> a")
  , (TyAll "a" (TyAll "b" (TyArr a b)), "forall a. forall b. a -> b")
  
  -- Records - updated for [(Name, Typ)]
  , (TyRcd [("x", int)], "{x : int}")
  , (TyRcd [("x", int), ("y", bool)], "{x : int, y : bool}")
  , (TyRcd [], "{}")
  
  -- Type context - updated for [TyCtxE]
  , (TyCtx [TypeN "x" int], "[x : int]")
  , (TyCtx [KindN "t"], "[t : Type]")
  , (TyCtx [TypeN "x" int, KindN "t"], "[x : int, t : Type]")
  , (TyCtx [TypeEqN "t" int], "[type t = int]")
  , (TyCtx [], "[]")
  
  -- Box types
  , (TyBoxT [] int, "[] ==> int")
  , (TyBoxT [TypeN "x" int] int, "[x : int] ==> int")
  , (TyBoxT [KindN "t", TypeN "x" (TyVar "t")] (TyVar "t"), "[t : Type, x : t] ==> t")
  
  -- Module types
  , (TyModule (TySig []), "sig  end")
  , (TyModule (TySig [ValDecl "x" int]), "sig val x : int end")
  , (TyModule (TyArrowM int (TySig [])), "int ->m sig  end")
  , (TyModule (ForallM "t" (TySig [])), "∀t. sig  end")
  ]
  where
    a = TyVar "a"
    b = TyVar "b"

prettyModuleTests :: [(Module, String)]
prettyModuleTests =
  [ (VarM "M", "M")
  , (Struct [] [], "struct  end")
  , (Struct [] [ExpEN "x" x], "struct x = x end")
  , (Struct [("M", int)] [], "struct import M : int;  end")
  , (Functor [("x", TmArgType int)] (VarM "M"), "functor (x : int) -> M")
  , (Functor [("t", TyArg)] (VarM "m"), "functor (type t) -> m")
  , (MApp (VarM "M1") (VarM "M2"), "M1 ^ M2")
  , (MAppt (VarM "M") int, "M ^@ int")
  , (MLink (VarM "M1") (VarM "M2"), "link(M1, M2)")
  ]

prettyTyCtxTests :: [(TyCtxE, String)]
prettyTyCtxTests =
  [ (TypeN "x" int, "x : int")
  , (Type int, "int")
  , (KindN "t", "t : Type")
  , (Kind, "Type")
  , (TypeEqN "t" int, "type t = int")
  , (TyMod "M" (TySig []), "module M : sig  end")
  , (TypeEqM "S" (TySig []), "module type S = sig  end")
  ]