module EnvML.Parser.ParserSpec (spec) where

import EnvML.Parser.AST
import EnvML.Parser.HappyAlex.Lexer (lexer)
import EnvML.Parser.HappyAlex.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import Test.Hspec

spec :: Spec
spec = do
  describe "EnvML.Parser (.eml / Modules)" $ do
    it "parses a simple let binding" $ do
      let input = "let x = 1;;"
      let expected = Struct [("x", ExpE (Lit (LitInt 1)))]
      parseModule (lexer input) `shouldBe` expected

    it "parses multiple bindings (let and type)" $ do
      let input = "let x = 1;; type t = int;;"
      let expected =
            Struct
              [ ("x", ExpE (Lit (LitInt 1))),
                ("t", TypE (TyLit TyInt))
              ]
      parseModule (lexer input) `shouldBe` expected

    it "parses empty struct" $ do
      let input = "struct end"
      let expected = Struct []
      parseModule (lexer input) `shouldBe` expected

    it "parses functor definition" $ do
      let input = "functor (x : sig end) -> struct end"
      let expected = Functor "x" (TyModule (TySig [])) (Struct [])
      parseModule (lexer input) `shouldBe` expected

    it "parses module application" $ do
      let input = "(functor (x : sig end) -> struct end) (struct end)"
      let expected = MApp (Functor "x" (TyModule (TySig [])) (Struct [])) (Struct [])
      parseModule (lexer input) `shouldBe` expected

    it "parses module linking" $ do
      let input = "link(struct end, struct end)"
      let expected = MLink (Struct []) (Struct [])
      parseModule (lexer input) `shouldBe` expected

  describe "EnvML.Parser (.emli / Interfaces)" $ do
    it "parses a simple val declaration" $ do
      let input = "val x : int;;"
      let expected = TySig [ValDecl "x" (TyLit TyInt)]
      parseModuleTyp (lexer input) `shouldBe` expected

    it "parses a type definition in an interface" $ do
      let input = "type t = int;;"
      let expected = TySig [TyDef "t" (TyLit TyInt)]
      parseModuleTyp (lexer input) `shouldBe` expected

    it "parses multiple declarations" $ do
      let input = "val x : int;; type t = int;;"
      let expected =
            TySig
              [ ValDecl "x" (TyLit TyInt),
                TyDef "t" (TyLit TyInt)
              ]
      parseModuleTyp (lexer input) `shouldBe` expected

    it "parses module declarations inside signatures" $ do
      let input = "module M : S;;"
      let expected = TySig [ModDecl "M" "S"]
      parseModuleTyp (lexer input) `shouldBe` expected

    it "parses module type definitions" $ do
      let input = "module type S = sig end;;"
      let expected = TySig [SigDecl "S" (TySig [])]
      parseModuleTyp (lexer input) `shouldBe` expected

    it "parses module type arrows" $ do
      let input = "int ->m sig end"
      let expected = TyArrowM (TyLit TyInt) (TySig [])
      parseModuleTyp (lexer input) `shouldBe` expected

  describe "EnvML.Parser (Expressions)" $ do
    it "parses integers" $ do
      parseExp (lexer "42") `shouldBe` Lit (LitInt 42)

    it "parses true bool" $ do
      parseExp (lexer "true") `shouldBe` Lit (LitBool True)

    it "parses false bool" $ do
      parseExp (lexer "false") `shouldBe` Lit (LitBool False)

    it "parses strings" $ do
      parseExp (lexer "\"hello\"") `shouldBe` Lit (LitStr "hello")

    it "parses variables" $ do
      parseExp (lexer "myVar") `shouldBe` Var "myVar"

    it "parses lambda functions" $ do
      let input = "fun (x: int) -> x"
      let expected = Lam "x" (TyLit TyInt) (Var "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses nested lambda functions" $ do
      let input = "fun (x: int) -> fun (y : int) -> y"
      let expected = Lam "x" (TyLit TyInt) (Lam "y" (TyLit TyInt) (Var "y"))
      parseExp (lexer input) `shouldBe` expected

    it "parses closure" $ do
      let input = "clos [type t = int, x = 1] (y: t) -> y"
      let expected =
            Clos
              [ ("t", TypE (TyLit TyInt)),
                ("x", ExpE (Lit (LitInt 1)))
              ]
              "y"
              (TyVar "t")
              (Var "y")
      parseExp (lexer input) `shouldBe` expected

    it "parses closure with empty env" $ do
      let input = "clos [] (y: t) -> y"
      let expected =
            Clos
              []
              "y"
              (TyVar "t")
              (Var "y")
      parseExp (lexer input) `shouldBe` expected

    it "parses function application" $ do
      let input = "f(x)"
      let expected = App (Var "f") (Var "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses nested function application (left associative)" $ do
      let input = "f(x)(y)"
      let expected = App (App (Var "f") (Var "x")) (Var "y")
      parseExp (lexer input) `shouldBe` expected

    it "parses type lambda functions" $ do
      let input = "fun type a -> x"
      let expected = TLam "a" (Var "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses nested type lambda functions" $ do
      let input = "fun type x -> fun type y -> y"
      let expected = TLam "x" (TLam "y" (Var "y"))
      parseExp (lexer input) `shouldBe` expected

    it "parses type closure" $ do
      let input = "clos [type t = int, x = 1] type y -> x"
      let expected =
            TClos
              [ ("t", TypE (TyLit TyInt)),
                ("x", ExpE (Lit (LitInt 1)))
              ]
              "y"
              (Var "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses type function application" $ do
      let input = "f<x>"
      let expected = TApp (Var "f") (TyVar "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses nested type function application (left associative)" $ do
      let input = "f<x><y>"
      let expected = TApp (TApp (Var "f") (TyVar "x")) (TyVar "y")
      parseExp (lexer input) `shouldBe` expected

    it "parses box construction" $ do
      let input = "box [type t = int, x = 1] in x"
      let expected =
            Box
              [ ("t", TypE (TyLit TyInt)),
                ("x", ExpE (Lit (LitInt 1)))
              ]
              (Var "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses record construction" $ do
      let input = "{label = 5}"
      let expected = Rec "label" (Lit (LitInt 5))
      parseExp (lexer input) `shouldBe` expected

    it "parses record projection" $ do
      let input = "x.label"
      let expected = RProj (Var "x") "label"
      parseExp (lexer input) `shouldBe` expected

    it "parses first-class environment" $ do
      let input = "[type t = int, x = 1]"
      let expected =
            FEnv
              [ ("t", TypE (TyLit TyInt)),
                ("x", ExpE (Lit (LitInt 1)))
              ]
      parseExp (lexer input) `shouldBe` expected

    it "parses type annotations" $ do
      let input = "(x :: int)"
      let expected = Anno (Var "x") (TyLit TyInt)
      parseExp (lexer input) `shouldBe` expected

    it "parses box construction + function" $ do
      let input = "box [type t = int, x = 1] in fun (y: t) -> x"
      let expected =
            Box
              [ ("t", TypE (TyLit TyInt)),
                ("x", ExpE (Lit (LitInt 1)))
              ]
              (Lam "y" (TyVar "t") (Var "x"))
      parseExp (lexer input) `shouldBe` expected

  describe "EnvML.Parser (Types)" $ do
    it "parses int type" $ do
      parseTyp (lexer "int") `shouldBe` TyLit TyInt

    it "parses string type" $ do
      parseTyp (lexer "string") `shouldBe` TyLit TyStr

    it "parses bool type" $ do
      parseTyp (lexer "bool") `shouldBe` TyLit TyBool

    it "parses type variables" $ do
      parseTyp (lexer "a") `shouldBe` TyVar "a"

    it "parses function types" $ do
      let input = "int -> int"
      let expected = TyArr (TyLit TyInt) (TyLit TyInt)
      parseTyp (lexer input) `shouldBe` expected

    it "parses nested function types (right associative)" $ do
      let input = "int -> int -> int"
      let expected = TyArr (TyLit TyInt) (TyArr (TyLit TyInt) (TyLit TyInt))
      parseTyp (lexer input) `shouldBe` expected

    it "parses forall types" $ do
      let input = "forall a. a"
      let expected = TyAll "a" (TyVar "a")
      parseTyp (lexer input) `shouldBe` expected

    it "parses nested forall types" $ do
      let input = "forall a. forall b. a"
      let expected = TyAll "a" (TyAll "b" (TyVar "a"))
      parseTyp (lexer input) `shouldBe` expected

    it "parses box arrow types" $ do
      let input = "[t : Type] ===> int"
      let expected = TyBoxT [("t", Kind)] (TyLit TyInt)
      parseTyp (lexer input) `shouldBe` expected

    it "parses record types" $ do
      let input = "{l : int}"
      let expected = TyRcd "l" (TyLit TyInt)
      parseTyp (lexer input) `shouldBe` expected

    it "parses substitution types" $ do
      let input = "[x:=int] int"
      let expected = TySubstT "x" (TyLit TyInt) (TyLit TyInt)
      parseTyp (lexer input) `shouldBe` expected

    it "parses environment types" $ do
      let input = "[x : Type, y : int, a : (int)=]"
      let expected =
            TyEnvt
              [ ("x", Kind),
                ("y", Type (TyLit TyInt)),
                ("a", TypeEq (TyLit TyInt))
              ]
      parseTyp (lexer input) `shouldBe` expected
