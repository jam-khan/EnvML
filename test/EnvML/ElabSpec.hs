{-# LANGUAGE ScopedTypeVariables #-}
module EnvML.ElabSpec (spec) where

import EnvML.Syntax as Src
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import EnvML.Elab
import qualified CoreFE.Named as Named
import qualified CoreFE.DeBruijn as DB
import qualified CoreFE.Syntax as CoreFE
import qualified CoreFE.Eval as Eval
import Test.Hspec

spec :: Spec
spec = do
  describe "Elaborate Simple Expressions" $ do

    it "elaborates variable" $ do
      let input = "x"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      -- Variable "x" at index 0 (assumes context [x])
      named `shouldBe` Right (Named.Var "x")

    it "elaborates integer literal" $ do
      let input = "42"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.Lit (CoreFE.LitInt 42))

    it "elaborates boolean literal" $ do
      let input = "true"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.Lit (CoreFE.LitBool True))

  describe "Elaborate Lambda Expressions" $ do

    it "elaborates single-arg lambda" $ do
      let input = "fun (x : int) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.Lam "x" (Named.Var "x"))

    it "elaborates multi-arg lambda to nested lambdas" $ do
      let input = "fun (x : int) (y : int) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.Lam "x" (Named.Lam "y" (Named.Var "x")))

    it "elaborates type lambda" $ do
      let input = "fun (type a) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.TLam "a" (Named.Var "x"))

    it "elaborates type arg followed by term arg" $ do
      let input = "fun (type a) (x : int) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.TLam "a" (Named.Lam "x" (Named.Var "x")))

    it "elaborates term arg followed by type arg" $ do
      let input = "fun (x : int) (type a) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.Lam "x" (Named.TLam "a" (Named.Var "x")))

    it "elaborates complex mixed args" $ do
      let input = "fun (type a) (x : a) (type b) (y : b) -> x"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.TLam "a"
                               (Named.Lam "x"
                                 (Named.TLam "b"
                                   (Named.Lam "y" (Named.Var "x")))))

  describe "Elaborate Applications" $ do

    it "elaborates function application" $ do
      let input = "f(x)"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.App (Named.Var "f") (Named.Var "x"))

    it "elaborates type application" $ do
      let input = "f @ int"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      named `shouldBe` Right (Named.TApp (Named.Var "f") (Named.TyLit CoreFE.TyInt))

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

  describe "Elaborate Modules" $ do

    it "elaborates module variable" $ do
      let m = Src.VarM "M"
      let named = elabModule m
      named `shouldBe` Right (Named.Var "M")

    -- Modules are sandboxed: every standalone struct / whole functor elaborates
    -- to an empty-environment box ([] ▷ e). A functor's body struct stays unboxed
    -- (it sits inside the functor's box).
    it "elaborates simple struct with let" $ do
      let input = "let x = 1;"
      let parsed = parseModule (lexer input)
      let named = elabModule parsed
      named `shouldBe`
        Right (Named.Box [] (Named.FEnv [Named.ModE "x" (Named.Lit (CoreFE.LitInt 1))]))

    it "elaborates functor with term argument" $ do
      let m = Src.Functor [("x", Src.TmArgType (Src.TyLit CoreFE.TyInt))]
                          (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Right (Named.Box [] (Named.Lam "x" (Named.FEnv [])))

    it "elaborates functor with type argument" $ do
      let m = Src.Functor [("t", Src.TyArg)] (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Right (Named.Box [] (Named.TLam "t" (Named.FEnv [])))

    it "elaborates multi-arg functor to nested" $ do
      let m = Src.Functor [("t", Src.TyArg), ("x", Src.TmArgType (Src.TyVar "t"))]
                          (Src.Struct [])
      let named = elabModule m
      named `shouldBe`
        Right (Named.Box [] (Named.TLam "t" (Named.Lam "x" (Named.FEnv []))))

  describe "Merge elaboration (no core concatenation primitive)" $ do

    -- Composition is expanded at elaboration time into an environment literal
    -- built from projections, so no concatenation node reaches CoreFE.
    it "expands ++ into projections out of both operands" $ do
      let input = "module a : sig val f : int; end = struct let f : int = 1; end; \
                  \module b : sig val g : int; end = struct let g : int = 2; end; \
                  \module c = a ++ b;"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left err -> expectationFailure ("elaboration failed: " ++ err)
        Right e  -> hasConcatShape e `shouldBe` True

    it "rejects a merge whose operands share a component" $ do
      let input = "module a : sig val f : int; end = struct let f : int = 1; end; \
                  \module b : sig val f : int; end = struct let f : int = 2; end; \
                  \module c = a ++ b;"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left _  -> return ()
        Right _ -> expectationFailure "expected a duplicate-component error"

    it "rejects a merge whose operand signature is unknown" $ do
      let input = "module f = functor (m) -> m ++ struct let g : int = 3; end;"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left _  -> return ()
        Right _ -> expectationFailure "expected an undetermined-signature error"

    -- Environment entries telescope, so an operand spliced into the merged
    -- environment would have its free variables captured by the other
    -- operand's component names. Operands are projected, never spliced.
    it "does not capture an ambient name with a component of the same name" $ do
      let input = "module f  = struct let z : int = 99; end; \
                  \module m1 : sig val f : int; end = struct let f : int = 1; end; \
                  \module r  = m1 + struct let h : int = (f.z :: int); end; \
                  \let out : int = (r.h :: int);"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left err -> expectationFailure ("elaboration failed: " ++ err)
        Right e  -> evalTop e `shouldBe` Just 99

    -- An operand contributing only type components still has to be evaluated:
    -- projecting nothing from it must not drop it from the program.
    it "keeps an operand that contributes no projectable component" $ do
      let input = "module m1 = struct let a : int = 1; end; \
                  \module mkT : ( sig val a : int; end ) ->m ( sig type t = int; end ) \
                  \  = functor (x) -> struct type t = int; end; \
                  \module m2 = m1 ++ mkT(m1);"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left err -> expectationFailure ("elaboration failed: " ++ err)
        Right e  -> mentionsVar "mkT" e `shouldBe` True

    -- A variable operand is used directly unless the merge introduces a
    -- component that would shadow it.
    it "does not let a component shadow the variable operand it came from" $ do
      let input = "module m1 : sig val m1 : int; end = struct let m1 : int = 7; end; \
                  \module m2 : sig val b  : int; end = struct let b  : int = 1; end; \
                  \module r = m1 ++ m2; \
                  \let out : int = (r.m1 :: int);"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left err -> expectationFailure ("elaboration failed: " ++ err)
        Right e  -> evalTop e `shouldBe` Just 7

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
        CoreFE.TLam _ -> return ()
        _ -> expectationFailure "Expected TLam"

-- | Does the elaborated program contain an environment literal that merges
--   projections out of two different sources? (A stand-in for "the merge was
--   expanded", since CoreFE no longer has a node to look for.)
hasConcatShape :: Named.Exp -> Bool
hasConcatShape = go
  where
    go (Named.Box env e)  = any goE env || go e
    go (Named.FEnv env)   = any isProj env || any goE env
    go (Named.Lam _ e)    = go e
    go (Named.TLam _ e)   = go e
    go (Named.App a b)    = go a || go b
    go (Named.TApp a _)   = go a
    go (Named.Anno a _)   = go a
    go (Named.Rec _ a)    = go a
    go (Named.RProj a _)  = go a
    go _                  = False

    goE (Named.ModE _ e) = go e
    goE (Named.ExpE _ e) = go e
    goE (Named.TypE _ _) = False

    isProj (Named.ModE _ (Named.RProj _ _)) = True
    isProj _                                = False

-- | Evaluate a whole program and read back the integer bound to @out@.
evalTop :: Named.Exp -> Maybe Int
evalTop e = Eval.eval [] (DB.toDeBruijn e) >>= lookupInt "out"

lookupInt :: String -> CoreFE.Exp -> Maybe Int
lookupInt label = go
  where
    go (CoreFE.Rec l e) | l == label = intOf e
                        | otherwise  = Nothing
    go (CoreFE.FEnv env) = firstJust (map goE env)
    go (CoreFE.Anno e _) = go e
    go _                 = Nothing

    goE (CoreFE.ExpE e) = go e
    goE (CoreFE.TypE _) = Nothing

    intOf (CoreFE.Lit (CoreFE.LitInt n)) = Just n
    intOf (CoreFE.Anno e _)              = intOf e
    intOf _                              = Nothing

    firstJust = foldr (\x acc -> maybe acc Just x) Nothing

-- | Does the elaborated program still reference this source name?
mentionsVar :: String -> Named.Exp -> Bool
mentionsVar name = go
  where
    go (Named.Var n)      = n == name
    go (Named.Box env e)  = any goE env || go e
    go (Named.FEnv env)   = any goE env
    go (Named.Lam _ e)    = go e
    go (Named.TLam _ e)   = go e
    go (Named.App a b)    = go a || go b
    go (Named.TApp a _)   = go a
    go (Named.Anno a _)   = go a
    go (Named.Rec _ a)    = go a
    go (Named.RProj a _)  = go a
    go _                  = False

    goE (Named.ModE _ e) = go e
    goE (Named.ExpE _ e) = go e
    goE (Named.TypE _ _) = False
