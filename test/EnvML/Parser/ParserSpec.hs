module EnvML.Parser.ParserSpec (spec) where

import EnvML.Parser.AST
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import Test.Hspec

spec :: Spec
spec = do
  describe "EnvML.Parser (.eml / Modules)" $ do
    it "parses let binding" $ do
      let input = "let x = 1;;"
      let expected = Struct [] [ExpEN "x" (Lit (LitInt 1))]
      parseModule (lexer input) `shouldBe` expected

    it "parses let binding with explicit type annotation" $ do
      let input = "let x : int = 1;;"
      let expected = Struct [] [ExpEN "x" (Anno (Lit (LitInt 1)) (TyLit TyInt))]
      parseModule (lexer input) `shouldBe` expected

    it "parses type binding" $ do
      let input = "type t = int;;"
      let expected = Struct [] [TypEN "t" (TyLit TyInt)]
      parseModule (lexer input) `shouldBe` expected

    it "parses module let binding" $ do
      let input = "module x = struct end;;"
      let expected = Struct [] [ModE "x" (Struct [] [])]
      parseModule (lexer input) `shouldBe` expected

    it "parses module let binding with explicit type annotation" $ do
      let input = "module x : sig end = struct end;;"
      let expected = Struct [] [ModE "x" (Struct [] [])]
      parseModule (lexer input) `shouldBe` expected

    it "parses module type binding" $ do
      let input = "module type x = sig end;;"
      let expected = Struct [] [ModTypE "x" (TySig [])]
      parseModule (lexer input) `shouldBe` expected

    it "parses multiple bindings" $ do
      let input = "let x = 1;; type t = int;; module y = struct end;; module type m = sig end;;"
      let expected =
            Struct
              []
              [ ExpEN "x" (Lit (LitInt 1)),
                TypEN "t" (TyLit TyInt),
                ModE "y" (Struct [] []),
                ModTypE "m" (TySig [])
              ]
      parseModule (lexer input) `shouldBe` expected

    it "parses empty struct" $ do
      let input = ""
      let expected = Struct [] []
      parseModule (lexer input) `shouldBe` expected

    it "parses single import" $ do
      let input = "import M : sig end;;"
      let expected = Struct [("M", TyModule (TySig []))] []
      parseModule (lexer input) `shouldBe` expected

    it "parses multiple imports" $ do
      let input = "import M : sig type t = int;; end, N : sig end;;"
      let expected = Struct [("M", TyModule (TySig [TyDef "t" (TyLit TyInt)])), ("N", TyModule (TySig []))] []
      parseModule (lexer input) `shouldBe` expected

  describe "EnvML.Parser (.emli / Interfaces)" $ do
    it "parses empty interface" $ do
      let input = ""
      let expected = TySig []
      parseModuleTyp (lexer input) `shouldBe` expected

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
      let input = "module M : sig end;;"
      let expected = TySig [ModDecl "M" (TySig [])]
      parseModuleTyp (lexer input) `shouldBe` expected

    it "parses module type definitions" $ do
      let input = "module type S = ;;"
      let expected = TySig [SigDecl "S" []]
      parseModuleTyp (lexer input) `shouldBe` expected

    it "parses functor declaration in signature" $ do
      let input = "functor M (x : int) : sig end;;"
      let expected = TySig [FunctorDecl "M" [("x", TmArgType (TyLit TyInt))] (TySig [])]
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
      let input = "fun (x) -> x"
      let expected = Lam [("x", TmArg)] (Var "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses nested lambda functions" $ do
      let input = "fun (x) -> fun (y) -> y"
      let expected = Lam [("x", TmArg)] (Lam [("y", TmArg)] (Var "y"))
      parseExp (lexer input) `shouldBe` expected

    it "parses closure" $ do
      let input = "clos [type t = int, x = 1] (y) -> y"
      let expected =
            Clos
              [ TypEN "t" (TyLit TyInt),
                ExpEN "x" (Lit (LitInt 1))
              ]
              [("y", TmArg)]
              (Var "y")
      parseExp (lexer input) `shouldBe` expected

    it "parses closure with empty env" $ do
      let input = "clos [] (y) -> y"
      let expected =
            Clos
              []
              [("y", TmArg)]
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
      let input = "fun (type a) -> x"
      let expected = Lam [("a", TyArg)] (Var "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses nested type lambda functions" $ do
      let input = "fun (type x) -> fun (type y) -> y"
      let expected = Lam [("x", TyArg)] (Lam [("y", TyArg)] (Var "y"))
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
              [ TypEN "t" (TyLit TyInt),
                ExpEN "x" (Lit (LitInt 1))
              ]
              (Var "x")
      parseExp (lexer input) `shouldBe` expected

    it "parses record construction" $ do
      let input = "{label = 5}"
      let expected = Rec [("label", Lit (LitInt 5))]
      parseExp (lexer input) `shouldBe` expected

    it "parses record with multiple fields" $ do
      let input = "{x = 1, y = 2}"
      let expected = Rec [("x", Lit (LitInt 1)), ("y", Lit (LitInt 2))]
      parseExp (lexer input) `shouldBe` expected

    it "parses record projection" $ do
      let input = "x.label"
      let expected = RProj (Var "x") "label"
      parseExp (lexer input) `shouldBe` expected

    it "parses first-class environment" $ do
      let input = "[type t = int, x = 1, module type M = sig end, module N = struct end]"
      let expected =
            FEnv
              [ TypEN "t" (TyLit TyInt),
                ExpEN "x" (Lit (LitInt 1)),
                ModTypE "M" (TySig []),
                ModE "N" (Struct [] [])
              ]
      parseExp (lexer input) `shouldBe` expected

    it "parses type annotations" $ do
      let input = "(x :: int)"
      let expected = Anno (Var "x") (TyLit TyInt)
      parseExp (lexer input) `shouldBe` expected

    it "parses box construction + function" $ do
      let input = "box [type t = int, x = 1] in fun (y) -> x"
      let expected =
            Box
              [ TypEN "t" (TyLit TyInt),
                ExpEN "x" (Lit (LitInt 1))
              ]
              (Lam [("y", TmArg)] (Var "x"))
      parseExp (lexer input) `shouldBe` expected

    it "parses functor definition" $ do
      let input = "functor (x : int) -> struct end"
      let expected = Mod $ Functor [("x", TmArgType (TyLit TyInt))] (Struct [] [])
      parseExp (lexer input) `shouldBe` expected

    it "parses module application" $ do
      let input = "(functor (x : int) -> struct end) (struct end)"
      let expected = Mod $ MApp (Functor [("x", TmArgType (TyLit TyInt))] (Struct [] [])) (Struct [] [])
      parseExp (lexer input) `shouldBe` expected

    it "parses module linking" $ do
      let input = "link(struct end, struct end)"
      let expected = Mod $ MLink (Struct [] []) (Struct [] [])
      parseExp (lexer input) `shouldBe` expected

    it "parses binary addition" $ do
      let input = "1 + 2"
      let expected = BinOp (Add (Lit (LitInt 1)) (Lit (LitInt 2)))
      parseExp (lexer input) `shouldBe` expected

    it "parses binary subtraction" $ do
      let input = "1 - 2"
      let expected = BinOp (Sub (Lit (LitInt 1)) (Lit (LitInt 2)))
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
      let expected = TyBoxT [KindN "t"] (TyLit TyInt)
      parseTyp (lexer input) `shouldBe` expected

    it "parses record types" $ do
      let input = "{l : int}"
      let expected = TyRcd [("l", TyLit TyInt)]
      parseTyp (lexer input) `shouldBe` expected

    it "parses record types with multiple fields" $ do
      let input = "{x : int, y : bool}"
      let expected = TyRcd [("x", TyLit TyInt), ("y", TyLit TyBool)]
      parseTyp (lexer input) `shouldBe` expected

    it "parses environment types" $ do
      let input = "[x : Type, y : int, type a = int]"
      let expected =
            TyCtx
              [ KindN "x",
                TypeN "y" (TyLit TyInt),
                TypeEqN "a" (TyLit TyInt)
              ]
      parseTyp (lexer input) `shouldBe` expected

    it "parses sig types (TyDef)" $ do
      let input = "sig type t = int;; end"
      let expected = TyModule (TySig [TyDef "t" (TyLit TyInt)])
      parseTyp (lexer input) `shouldBe` expected

    it "parses sig types (ValDecl)" $ do
      let input = "sig val x : int;; end"
      let expected = TyModule (TySig [ValDecl "x" (TyLit TyInt)])
      parseTyp (lexer input) `shouldBe` expected

    it "parses sig types (ModDecl)" $ do
      let input = "sig module M : sig end;; end"
      let expected = TyModule (TySig [ModDecl "M" (TySig [])])
      parseTyp (lexer input) `shouldBe` expected

    it "parses sig types (SigDecl)" $ do
      let input = "sig module type S = ;; end"
      let expected = TyModule (TySig [SigDecl "S" []])
      parseTyp (lexer input) `shouldBe` expected

    it "parses sig types with multiple declarations" $ do
      let input = "sig val x : int;; type t = int;; end"
      let expected =
            TyModule
              ( TySig
                  [ ValDecl "x" (TyLit TyInt),
                    TyDef "t" (TyLit TyInt)
                  ]
              )
      parseTyp (lexer input) `shouldBe` expected

    it "parses module type arrows" $ do
      let input = "int ->m sig end"
      let expected = TyModule $ TyArrowM (TyLit TyInt) (TySig [])
      parseTyp (lexer input) `shouldBe` expected

    it "parses forall module types" $ do
      let input = "forall t. sig end"
      let expected = TyModule $ ForallM "t" (TySig [])
      parseTyp (lexer input) `shouldBe` expected