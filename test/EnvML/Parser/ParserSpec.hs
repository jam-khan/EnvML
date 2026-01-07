module EnvML.Parser.ParserSpec (spec) where

import Test.Hspec
import EnvML.Parser.AST
import EnvML.Parser.HappyAlex.Lexer (lexer)
import EnvML.Parser.HappyAlex.Parser (parseModule, parseModuleTyp, parseExp, parseTyp)

spec :: Spec
spec = do
  describe "EnvML.Parser (.eml / Modules)" $ do
    it "parses a simple let binding" $ do
      let input = "let x = 1;;"
      let expected = Struct [("x", ExpE (Lit (LitInt 1)))]
      parseModule (lexer input) `shouldBe` expected

    it "parses multiple bindings (let and type)" $ do
      let input = "let x = 1;; type t = int;;"
      let expected = Struct 
            [ ("x", ExpE (Lit (LitInt 1)))
            , ("t", TypE (TyLit TyInt))
            ]
      parseModule (lexer input) `shouldBe` expected

    -- -- [ADDED] Test for Functor syntax
    -- it "parses a functor definition" $ do
    --   let input = "functor (X : sig end) struct end"
    --   let expected = Functor "X" (TySig []) (Struct [])
    --   parseModule (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Module Linking/Merging syntax
    -- it "parses module linking" $ do
    --   let input = "(struct end) |><| (struct end)"
    --   let expected = MLink (Struct []) (Struct [])
    --   parseModule (lexer input) `shouldBe` expected

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
      let expected = TySig 
            [ ValDecl "x" (TyLit TyInt)
            , TyDef "t" (TyLit TyInt)
            ]
      parseModuleTyp (lexer input) `shouldBe` expected

    -- -- [ADDED] Test for Module declarations in interfaces
    -- it "parses module declarations inside signatures" $ do
    --   let input = "module M : S;;"
    --   let expected = TySig [ModDecl "M" "S"]
    --   parseModuleTyp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Module Type definitions
    -- it "parses module type definitions" $ do
    --   let input = "module type S = sig end;;"
    --   let expected = TySig [SigDecl "S" (TySig [])]
    --   parseModuleTyp (lexer input) `shouldBe` expected

  describe "EnvML.Parser (Expressions)" $ do
    it "parses integers" $ do
      parseExp (lexer "42") `shouldBe` Lit (LitInt 42)

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
      let expected = Clos 
            [ ("t", TypE (TyLit TyInt))
            , ("x", ExpE (Lit (LitInt 1)))
            ] "y" (TyVar "t") (Var "y")
      parseExp (lexer input) `shouldBe` expected


    it "parses closure with empty env" $ do
      let input = "clos [] (y: t) -> y"
      let expected = Clos 
            [] "y" (TyVar "t") (Var "y")
      parseExp (lexer input) `shouldBe` expected

    -- -- [ADDED] Test for Function Application
    -- -- Note: Assuming syntax f(x) based on your AST Show instance
    -- it "parses function application" $ do
    --   let input = "f(x)" 
    --   let expected = App (Var "f") (Var "x")
    --   parseExp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Record construction
    -- it "parses record construction" $ do
    --   let input = "{label = 5}"
    --   let expected = Rec "label" (Lit (LitInt 5))
    --   parseExp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Record Projection
    -- it "parses record projection" $ do
    --   let input = "x.label"
    --   let expected = RProj (Var "x") "label"
    --   parseExp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Type Abstraction (Big Lambda)
    -- it "parses type abstraction" $ do
    --   let input = "fun type a -> x"
    --   let expected = TLam "a" (Var "x")
    --   parseExp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Type Application
    -- it "parses type application" $ do
    --   let input = "f<int>"
    --   let expected = TApp (Var "f") (TyLit TyInt)
    --   parseExp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Box (Contextual packaging)
    -- it "parses box construction with environment" $ do
    --   -- Assuming environment syntax based on AST: [type t = int, x = 1]
    --   let input = "box [type t = int, x = 1] in x"
    --   let expected = Box 
    --         [ ("t", TypE (TyLit TyInt))
    --         , ("x", ExpE (Lit (LitInt 1)))
    --         ] (Var "x")
    --   parseExp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Type Annotation
    -- it "parses type annotations" $ do
    --   let input = "(x :: int)"
    --   let expected = Anno (Var "x") (TyLit TyInt)
    --   parseExp (lexer input) `shouldBe` expected

  describe "EnvML.Parser (Types)" $ do
    it "parses base types" $ do
      parseTyp (lexer "int") `shouldBe` TyLit TyInt

    it "parses function types" $ do
      let input = "int -> int"
      let expected = TyArr (TyLit TyInt) (TyLit TyInt)
      parseTyp (lexer input) `shouldBe` expected

    it "parses nested function types (right associative)" $ do
      let input = "int -> int -> int"
      -- int -> (int -> int)
      let expected = TyArr (TyLit TyInt) (TyArr (TyLit TyInt) (TyLit TyInt))
      parseTyp (lexer input) `shouldBe` expected

    -- -- [ADDED] Test for Type Variables
    -- it "parses type variables" $ do
    --   parseTyp (lexer "a") `shouldBe` TyVar "a"
    --
    -- -- [ADDED] Test for Universal Quantification (Forall)
    -- it "parses forall types" $ do
    --   let input = "forall a. a"
    --   let expected = TyAll "a" (TyVar "a")
    --   parseTyp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Record Types
    -- it "parses record types" $ do
    --   let input = "{l : int}"
    --   let expected = TyRcd "l" (TyLit TyInt)
    --   parseTyp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Contextual Arrow (Box Type)
    -- -- Syntax derived from Show instance: [env] ===> T
    -- it "parses contextual arrow types" $ do
    --   let input = "[t : Type] ===> int"
    --   let expected = TyBoxT [("t", Kind)] (TyLit TyInt)
    --   parseTyp (lexer input) `shouldBe` expected
    --
    -- -- [ADDED] Test for Substitution Types
    -- it "parses substitution types" $ do
    --   let input = "[x:=int] bool"
    --   let expected = TySubstT "x" (TyLit TyInt) (TyLit TyBool)
    --   parseTyp (lexer input) `shouldBe` expected
