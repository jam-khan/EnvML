module EnvML.Parser.DesugarSpec (spec) where

import EnvML.Parser.AST
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import Test.Hspec

spec :: Spec
spec = do
  describe "Desugar Lambda Expressions" $ do
    it "desugars multi-arg term lambda to nested Lam" $ do
      let input = "fun (x : int) (y : int) -> x"
      let parsed = parseExp (lexer input)
      let expected = Lam [("x", TmArgType (TyLit TyInt))]
                         (Lam [("y", TmArgType (TyLit TyInt))]
                              (Var "x"))
      desugarExp parsed `shouldBe` expected

    it "desugars single type arg to TLam" $ do
      let input = "fun (type a) -> x"
      let parsed = parseExp (lexer input)
      let expected = TLam [("a", TyArg)] (Var "x")
      desugarExp parsed `shouldBe` expected

    it "desugars type arg followed by term arg" $ do
      let input = "fun (type a) (x : int) -> x"
      let parsed = parseExp (lexer input)
      let expected = TLam [("a", TyArg)]
                          (Lam [("x", TmArgType (TyLit TyInt))]
                               (Var "x"))
      desugarExp parsed `shouldBe` expected

    it "desugars term arg followed by type arg" $ do
      let input = "fun (x : int) (type a) -> x"
      let parsed = parseExp (lexer input)
      let expected = Lam [("x", TmArgType (TyLit TyInt))]
                         (TLam [("a", TyArg)]
                               (Var "x"))
      desugarExp parsed `shouldBe` expected

    it "desugars mixed type and term args" $ do
      let input = "fun (type a) (x : a) (type b) (y : b) -> x"
      let parsed = parseExp (lexer input)
      let expected = TLam [("a", TyArg)]
                          (Lam [("x", TmArgType (TyVar "a"))]
                               (TLam [("b", TyArg)]
                                    (Lam [("y", TmArgType (TyVar "b"))]
                                         (Var "x"))))
      desugarExp parsed `shouldBe` expected

  describe "Desugar Closures" $ do
    it "desugars closure with type lambda body" $ do
      let input = "clos [x = 1] (type a) (y : int) -> y"
      let parsed = parseExp (lexer input)
      let expected = Clos [ExpEN "x" (Lit (LitInt 1))]
                          []
                          (TLam [("a", TyArg)]
                                (Lam [("y", TmArgType (TyLit TyInt))]
                                     (Var "y")))
      desugarExp parsed `shouldBe` expected

  describe "Desugar Functors" $ do
    it "desugars multi-arg term functor to nested" $ do
      let input = "module F = functor (x : int) (y : int) -> struct end;"
      let parsed = parseModule (lexer input)
      let expected = Struct [ModStruct "F" Nothing
                                      (Functor [("x", TmArgType (TyLit TyInt))]
                                               (Functor [("y", TmArgType (TyLit TyInt))]
                                                        (Struct [])))]
      desugarModule parsed `shouldBe` expected

    it "desugars mixed type/term functor args" $ do
      let input = "module F = functor (type t) (x : t) -> struct end;"
      let parsed = parseModule (lexer input)
      let expected = Struct [ModStruct "F" Nothing
                                      (Functor [("t", TyArg)]
                                               (Functor [("x", TmArgType (TyVar "t"))]
                                                        (Struct [])))]
      desugarModule parsed `shouldBe` expected

  describe "Desugar Interface FunctorDecl" $ do
    it "converts term arg FunctorDecl to ModDecl with TyArr" $ do
      let input = "functor F (x : int) : sig end;"
      let parsed = parseModuleTyp (lexer input)
      let expected = TySig [ModDecl "F" (TyArr (TyLit TyInt) 
                                                (TyModule (TySig [])))]
      desugarModuleTyp parsed `shouldBe` expected

    it "converts type arg FunctorDecl to ModDecl with TyAll" $ do
      let input = "functor F (type t) : sig end;"
      let parsed = parseModuleTyp (lexer input)
      let expected = TySig [ModDecl "F" (TyAll "t" (TyModule (TySig [])))]
      desugarModuleTyp parsed `shouldBe` expected

    it "converts multi-arg FunctorDecl with mixed args" $ do
      let input = "functor F (type t) (x : t) : sig end;"
      let parsed = parseModuleTyp (lexer input)
      let expected = TySig [ModDecl "F" 
                                   (TyAll "t"
                                         (TyArr (TyVar "t")
                                                (TyModule (TySig []))))]
      desugarModuleTyp parsed `shouldBe` expected

  describe "Idempotence" $ do
    it "is idempotent for nested lambdas" $ do
      let input = "fun (x : int) (y : int) -> x"
      let parsed = parseExp (lexer input)
      let desugared1 = desugarExp parsed
      let desugared2 = desugarExp desugared1
      desugared1 `shouldBe` desugared2

    it "is idempotent for mixed type/term lambdas" $ do
      let input = "fun (type a) (x : a) -> x"
      let parsed = parseExp (lexer input)
      let desugared1 = desugarExp parsed
      let desugared2 = desugarExp desugared1
      desugared1 `shouldBe` desugared2