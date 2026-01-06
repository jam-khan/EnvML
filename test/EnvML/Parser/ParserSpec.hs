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

  describe "EnvML.Parser (Expressions)" $ do
    it "parses integers" $ do
      parseExp (lexer "42") `shouldBe` Lit (LitInt 42)

    it "parses variables" $ do
      parseExp (lexer "myVar") `shouldBe` Var "myVar"

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