{-# LANGUAGE ScopedTypeVariables #-}
module EnvML.ElabSpec (spec) where

import EnvML.Syntax as Src
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import EnvML.Elab
import qualified CoreFE.Named as Named
import qualified CoreFE.DeBruijn as DB
import qualified CoreFE.Syntax as CoreFE
import Control.Exception (evaluate)
import Test.Hspec

spec :: Spec
spec = do
  describe "Elaborate Simple Expressions" $ do
    
    it "elaborates variable" $ do
      let input = "x"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      -- Variable "x" at index 0 (assumes context [x])
      named `shouldBe` Named.Var "x"

    it "elaborates integer literal" $ do
      let input = "42"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.Lit (CoreFE.LitInt 42)

    it "elaborates boolean literal" $ do
      let input = "true"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.Lit (CoreFE.LitBool True)

    it "elaborates if expression" $ do
      let input = "if true then 1 else 0"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe`
        Named.If
          (Named.Lit (CoreFE.LitBool True))
          (Named.Lit (CoreFE.LitInt 1))
          (Named.Lit (CoreFE.LitInt 0))

  describe "Elaborate Lambda Expressions" $ do
    
    it "elaborates single-arg lambda" $ do
      let input = "fun (x : int) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.Lam "x" (Named.Var "x")

    it "elaborates multi-arg lambda to nested lambdas" $ do
      let input = "fun (x : int) (y : int) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.Lam "x" (Named.Lam "y" (Named.Var "x"))

    it "elaborates type lambda" $ do
      let input = "fun (type a) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.TLam "a" (Named.Var "x")

    it "elaborates type arg followed by term arg" $ do
      let input = "fun (type a) (x : int) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.TLam "a" (Named.Lam "x" (Named.Var "x"))

    it "elaborates term arg followed by type arg" $ do
      let input = "fun (x : int) (type a) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.Lam "x" (Named.TLam "a" (Named.Var "x"))

    it "elaborates complex mixed args" $ do
      let input = "fun (type a) (x : a) (type b) (y : b) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.TLam "a" 
                         (Named.Lam "x" 
                           (Named.TLam "b" 
                             (Named.Lam "y" (Named.Var "x"))))

  describe "Elaborate Applications" $ do
    
    it "elaborates function application" $ do
      let input = "f(x)"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.App (Named.Var "f") (Named.Var "x")

    it "elaborates type application" $ do
      let input = "f @ int"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.TApp (Named.Var "f") (Named.TyLit CoreFE.TyInt)

    it "elaborates named fixpoint" $ do
      let input = "fix f. fun (x : int) -> f(x)"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe`
        Named.Fix "f" (Named.Lam "x" (Named.App (Named.Var "f") (Named.Var "x")))

    it "elaborates data constructor with source-level type annotation into core fold" $ do
      let input = "Nil(0) as NatList"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named
        `shouldBe` Named.Fold
          (Named.TyVar "NatList")
          (Named.DataCon "Nil" (Named.Lit (CoreFE.LitInt 0)))

    it "elaborates case by inserting core unfold on the scrutinee" $ do
      let input = "case xs of | <Nil=h> => h | <Cons=t> => t"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named
        `shouldBe` Named.Case
          (Named.Unfold (Named.Var "xs"))
          [ Named.CaseBranch "Nil" "h" (Named.Var "h")
          , Named.CaseBranch "Cons" "t" (Named.Var "t")
          ]

    it "elaborates wildcard case branch" $ do
      let input = "case xs of | _ => 0"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named
        `shouldBe` Named.Case
          (Named.Unfold (Named.Var "xs"))
          [Named.CaseBranch "_" "" (Named.Lit (CoreFE.LitInt 0))]

  describe "Elaborate Binary Operators" $ do

    it "elaborates comparison operators" $ do
      let input = "1 <= 2"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe`
        Named.BinOp
          (Named.Le
            (Named.Lit (CoreFE.LitInt 1))
            (Named.Lit (CoreFE.LitInt 2)))

    it "elaborates inequality operator" $ do
      let input = "x != y"
      let parsed = parseExp (lexer input)
      let named = elabExp parsed
      named `shouldBe` Named.BinOp (Named.Neq (Named.Var "x") (Named.Var "y"))

  describe "Elaborate Types" $ do
    
    it "elaborates type literals" $ do
      let input = "int"
      let parsed = parseTyp (lexer input)
      let named = elabTyp parsed
      named `shouldBe` Named.TyLit CoreFE.TyInt

    it "elaborates arrow types" $ do
      let input = "int -> bool"
      let parsed = parseTyp (lexer input)
      let named = elabTyp parsed
      named `shouldBe` Named.TyArr (Named.TyLit CoreFE.TyInt) (Named.TyLit CoreFE.TyBool)

    it "elaborates forall types" $ do
      let input = "forall a. (a -> a)"
      let parsed = parseTyp (lexer input)
      let named = elabTyp parsed
      named `shouldBe` Named.TyAll "a" (Named.TyArr (Named.TyVar "a") (Named.TyVar "a"))

    it "elaborates nested forall" $ do
      let input = "forall a. forall b. (a -> b)"
      let parsed = parseTyp (lexer input)
      let named = elabTyp parsed
      named `shouldBe` Named.TyAll "a" 
                         (Named.TyAll "b" 
                           (Named.TyArr (Named.TyVar "a") (Named.TyVar "b")))

    it "rejects inline sum annotations without a declared binder" $ do
      let sumTy = Src.TySum [("Nil", Src.TyLit CoreFE.TyInt), ("Cons", Src.TyVar "NatList")]
      evaluate
        (case elabTyp sumTy of
          Named.TyMu binder _ -> length binder
          _ -> 0)
        `shouldThrow` anyErrorCall

  describe "Elaborate Modules" $ do
    
    it "elaborates module variable" $ do
      let m = Src.VarM "M"
      let named = elabModule m
      named `shouldBe` Named.Var "M"

    it "elaborates simple struct with let" $ do
      let input = "let x = 1;"
      let parsed = parseModule (lexer input)
      let named = elabModule parsed
      named `shouldBe` Named.FEnv [Named.ModE "x" (Named.Lit (CoreFE.LitInt 1))]

    it "wraps type declarations of sum types with the declared binder in core" $ do
      let input = "type NatList = Nil as int | Cons as NatList;"
      let parsed = parseModule (lexer input)
      let named = elabModule parsed
      named
        `shouldBe` Named.FEnv
          [ Named.TypE
              "NatList"
              (Named.TyMu
                "NatList"
                (Named.TySum
                  [ ("Nil", Named.TyLit CoreFE.TyInt)
                  , ("Cons", Named.TyVar "NatList")
                  ]))
          ]

    it "elaborates functor with term argument" $ do
      let m = Src.Functor [("x", Src.TmArgType (Src.TyLit CoreFE.TyInt))]
                          (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Named.Lam "x" (Named.FEnv [])

    it "elaborates functor with type argument" $ do
      let m = Src.Functor [("t", Src.TyArg)] (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Named.TLam "t" (Named.FEnv [])

    it "elaborates multi-arg functor to nested" $ do
      let m = Src.Functor [("t", Src.TyArg), ("x", Src.TmArgType (Src.TyVar "t"))]
                          (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Named.TLam "t" (Named.Lam "x" (Named.FEnv []))

  describe "De Bruijn Conversion" $ do
    
    it "converts simple lambda" $ do
      let named = Named.Lam "x" (Named.Var "x")
      let nameless = DB.toDeBruijn named
      nameless `shouldBe` CoreFE.Lam (CoreFE.Var 0)

    it "converts nested lambda with outer reference" $ do
      let named = Named.Lam "x" (Named.Lam "y" (Named.Var "x"))
      let nameless = DB.toDeBruijn named
      nameless `shouldBe` CoreFE.Lam (CoreFE.Lam (CoreFE.Var 1))

    it "converts type lambda" $ do
      let named = Named.TLam "a" (Named.Var "x")
      -- Assumes "x" is in context at index 0
      let nameless = DB.toDeBruijn named
      case nameless of
        CoreFE.TLam body -> return ()
        _ -> expectationFailure "Expected TLam"

    it "converts if expression" $ do
      let named =
            Named.If
              (Named.Lit (CoreFE.LitBool True))
              (Named.Lit (CoreFE.LitInt 1))
              (Named.Lit (CoreFE.LitInt 0))
      let nameless = DB.toDeBruijn named
      nameless `shouldBe`
        CoreFE.If
          (CoreFE.Lit (CoreFE.LitBool True))
          (CoreFE.Lit (CoreFE.LitInt 1))
          (CoreFE.Lit (CoreFE.LitInt 0))

    it "converts named fixpoint with recursive reference" $ do
      let named =
            Named.Fix "f"
              (Named.Lam "x" (Named.App (Named.Var "f") (Named.Var "x")))
      let nameless = DB.toDeBruijn named
      nameless `shouldBe`
        CoreFE.Fix
          (CoreFE.Lam
            (CoreFE.App (CoreFE.Var 1) (CoreFE.Var 0)))