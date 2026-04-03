{-# LANGUAGE ScopedTypeVariables #-}
module EnvML.ElabSpec (spec) where

import EnvML.Syntax as Src
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import EnvML.Elab
import EnvML.Desugar (desugarExp, desugarModule)
import qualified EnvML.Desugared as D
import qualified CoreFE.Named as Named
import qualified CoreFE.DeBruijn as DB
import qualified CoreFE.Syntax as CoreFE
import Test.Hspec

-- | Parse and desugar an expression (all elab tests go through desugaring now)
pde :: String -> D.Exp
pde input = desugarExp (parseExp (lexer input))

-- | Parse and desugar a module
pdm :: String -> D.Module
pdm input = desugarModule (parseModule (lexer input))

spec :: Spec
spec = do
  describe "Elaborate Simple Expressions" $ do
    
    it "elaborates variable" $ do
      let named = elabExp (pde "x")
      named `shouldBe` Named.Var "x"

    it "elaborates integer literal" $ do
      let named = elabExp (pde "42")
      named `shouldBe` Named.Lit (CoreFE.LitInt 42)

    it "elaborates boolean literal" $ do
      let named = elabExp (pde "true")
      named `shouldBe` Named.Lit (CoreFE.LitBool True)

    it "elaborates if expression" $ do
      let named = elabExp (pde "if true then 1 else 0")
      named `shouldBe`
        Named.If
          (Named.Lit (CoreFE.LitBool True))
          (Named.Lit (CoreFE.LitInt 1))
          (Named.Lit (CoreFE.LitInt 0))

  describe "Elaborate Lambda Expressions" $ do
    
    it "elaborates single-arg lambda" $ do
      let named = elabExp (pde "fun (x : int) -> x")
      named `shouldBe` Named.Lam "x" (Named.Var "x")

    it "elaborates multi-arg lambda to nested lambdas" $ do
      let named = elabExp (pde "fun (x : int) (y : int) -> x")
      named `shouldBe` Named.Lam "x" (Named.Lam "y" (Named.Var "x"))

    it "elaborates type lambda" $ do
      let named = elabExp (pde "fun (type a) -> x")
      named `shouldBe` Named.TLam "a" (Named.Var "x")

    it "elaborates type arg followed by term arg" $ do
      let named = elabExp (pde "fun (type a) (x : int) -> x")
      named `shouldBe` Named.TLam "a" (Named.Lam "x" (Named.Var "x"))

    it "elaborates term arg followed by type arg" $ do
      let named = elabExp (pde "fun (x : int) (type a) -> x")
      named `shouldBe` Named.Lam "x" (Named.TLam "a" (Named.Var "x"))

    it "elaborates complex mixed args" $ do
      let named = elabExp (pde "fun (type a) (x : a) (type b) (y : b) -> x")
      named `shouldBe` Named.TLam "a" 
                         (Named.Lam "x" 
                           (Named.TLam "b" 
                             (Named.Lam "y" (Named.Var "x"))))

  describe "Elaborate Applications" $ do
    
    it "elaborates function application" $ do
      let named = elabExp (pde "f(x)")
      named `shouldBe` Named.App (Named.Var "f") (Named.Var "x")

    it "elaborates type application" $ do
      let named = elabExp (pde "f @ int")
      named `shouldBe` Named.TApp (Named.Var "f") (Named.TyLit CoreFE.TyInt)

    it "elaborates named fixpoint" $ do
      let named = elabExp (pde "fix f. fun (x : int) -> f(x)")
      named `shouldBe`
        Named.Fix "f" (Named.Lam "x" (Named.App (Named.Var "f") (Named.Var "x")))

    it "elaborates data constructor with source-level type annotation into core fold" $ do
      let named = elabExp (pde "Nil(0) as NatList")
      named
        `shouldBe` Named.Fold
          (Named.TyVar "NatList")
          (Named.DataCon "Nil" (Named.Lit (CoreFE.LitInt 0)))

    it "elaborates case by inserting core unfold on the scrutinee" $ do
      let named = elabExp (pde "case xs of | <Nil=h> => h | <Cons=t> => t")
      named
        `shouldBe` Named.Case
          (Named.Unfold (Named.Var "xs"))
          [ Named.CaseBranch "Nil" "h" (Named.Var "h")
          , Named.CaseBranch "Cons" "t" (Named.Var "t")
          ]

    it "elaborates wildcard case branch" $ do
      let named = elabExp (pde "case xs of | _ => 0")
      named
        `shouldBe` Named.Case
          (Named.Unfold (Named.Var "xs"))
          [Named.CaseBranch "_" "" (Named.Lit (CoreFE.LitInt 0))]

  describe "Elaborate Binary Operators" $ do

    it "elaborates comparison operators" $ do
      let named = elabExp (pde "1 <= 2")
      named `shouldBe`
        Named.BinOp
          (Named.Le
            (Named.Lit (CoreFE.LitInt 1))
            (Named.Lit (CoreFE.LitInt 2)))

    it "elaborates inequality operator" $ do
      let named = elabExp (pde "x != y")
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

    it "elaborates inline sum type without TyMu wrapping" $ do
      let sumTy = Src.TySum [("Nil", Src.TyLit CoreFE.TyInt), ("Cons", Src.TyVar "NatList")]
      elabTyp sumTy
        `shouldBe` Named.TySum
          [ ("Nil", Named.TyLit CoreFE.TyInt)
          , ("Cons", Named.TyVar "NatList")
          ]

  describe "Elaborate Modules" $ do
    
    it "elaborates module variable" $ do
      let named = elabModule (D.VarM "M")
      named `shouldBe` Named.Var "M"

    it "elaborates simple struct with let" $ do
      let named = elabModule (pdm "let x = 1;")
      named `shouldBe` Named.FEnv [Named.ModE "x" (Named.Lit (CoreFE.LitInt 1))]

    it "wraps type declarations of sum types with the declared binder in core" $ do
      let named = elabModule (pdm "type NatList = Nil as int | Cons as NatList;")
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
      let m = desugarModule $ Src.Functor [("x", Src.TmArgType (Src.TyLit CoreFE.TyInt))]
                                           (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Named.Lam "x" (Named.FEnv [])

    it "elaborates functor with type argument" $ do
      let m = desugarModule $ Src.Functor [("t", Src.TyArg)] (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Named.TLam "t" (Named.FEnv [])

    it "elaborates multi-arg functor to nested" $ do
      let m = desugarModule $ Src.Functor [("t", Src.TyArg), ("x", Src.TmArgType (Src.TyVar "t"))]
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