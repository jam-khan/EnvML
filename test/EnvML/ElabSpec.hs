{-# LANGUAGE ScopedTypeVariables #-}
module EnvML.ElabSpec (spec) where

import EnvML.Syntax as Src
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseTyp)
import EnvML.Elab
import qualified CoreFE.Named as N
import qualified CoreFE.DeBruijn as DB
import qualified CoreFE.Syntax as C
import qualified CoreFE.Check as Check
import qualified CoreFE.Eval as Eval
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM_)
import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import System.FilePath ((</>))
import Test.Hspec

-- Parse and elaborate in one step
elabE :: String -> Either ElabError N.Exp
elabE = elabExp [] . parseExp . lexer

elabT :: String -> Either ElabError N.Typ
elabT = elabTyp . parseTyp . lexer

elabM :: String -> Either ElabError N.Exp
elabM = elabModule . parseModule . lexer

spec :: Spec
spec = do
  describe "Elaborate Simple Expressions" $ do

    it "elaborates variable" $ do
      let input = "x"
      let parsed = parseExp (lexer input)
      let named = elabExp [] parsed
      -- Variable "x" at index 0 (assumes context [x])
      named `shouldBe` Right (N.Var "x")

    it "elaborates integer literal" $
      elabE "42" `shouldBe` Right (N.Lit (C.LitInt 42))

    it "elaborates boolean literal" $
      elabE "true" `shouldBe` Right (N.Lit (C.LitBool True))

  describe "Elaborate Lambda Expressions" $ do

    it "elaborates single-arg lambda" $
      elabE "fun (x : int) -> x" `shouldBe` Right (N.Lam "x" (N.Var "x"))

    it "elaborates multi-arg lambda to nested lambdas" $
      elabE "fun (x : int) (y : int) -> x" `shouldBe` Right (N.Lam "x" (N.Lam "y" (N.Var "x")))

    it "elaborates type lambda" $
      elabE "fun (type a) -> x" `shouldBe` Right (N.TLam "a" (N.Var "x"))

    it "elaborates type arg followed by term arg" $
      elabE "fun (type a) (x : int) -> x" `shouldBe` Right (N.TLam "a" (N.Lam "x" (N.Var "x")))

    it "elaborates term arg followed by type arg" $
      elabE "fun (x : int) (type a) -> x" `shouldBe` Right (N.Lam "x" (N.TLam "a" (N.Var "x")))

    it "elaborates complex mixed args" $
      elabE "fun (type a) (x : a) (type b) (y : b) -> x" `shouldBe` Right (N.TLam "a"
                               (N.Lam "x"
                                 (N.TLam "b"
                                   (N.Lam "y" (N.Var "x")))))

  describe "Elaborate Applications" $ do

    it "elaborates function application" $
      elabE "f(x)" `shouldBe` Right (N.App (N.Var "f") (N.Var "x"))

    it "elaborates type application" $
      elabE "f @ int" `shouldBe` Right (N.TApp (N.Var "f") (N.TyLit C.TyInt))

  describe "Elaborate Types" $ do

    it "elaborates type literals" $
      elabT "int" `shouldBe` Right (N.TyLit C.TyInt)

    it "elaborates arrow types" $
      elabT "int -> bool" `shouldBe` Right (N.TyArr (N.TyLit C.TyInt) (N.TyLit C.TyBool))

    it "elaborates forall types" $
      elabT "forall a. (a -> a)" `shouldBe` Right (N.TyAll "a" (N.TyArr (N.TyVar "a") (N.TyVar "a")))

    it "elaborates nested forall" $
      elabT "forall a. forall b. (a -> b)" `shouldBe` Right (N.TyAll "a"
                         (N.TyAll "b"
                           (N.TyArr (N.TyVar "a") (N.TyVar "b"))))

    -- A functor member of a signature is a term component, like a value or a
    -- module member: a labelled record type, not a manifest type binding.
    it "elaborates a functor declaration as a labelled term component" $ do
      let parsed = parseModuleTyp' "sig functor f (type t) (x : t) : sig val v : t; end; end"
      elabModTyp parsed `shouldBe`
        Right (N.TyEnvt
                 [ N.Type "f"
                     (N.TyRcd "f"
                        (N.TyAll "t"
                           (N.TyArr (N.TyVar "t")
                              (N.TyEnvt [N.Type "v" (N.TyRcd "v" (N.TyVar "t"))]))))
                 ])

    -- A module entry of an environment is a labelled record entry, so a module
    -- declared in a type context is a labelled record type.
    it "elaborates a module declaration in a type context as a labelled entry" $ do
      let parsed = parseTyp (lexer "[module m : sig val x : int; end]")
      elabTyp parsed `shouldBe`
        Right (N.TyEnvt
                 [ N.Type "m"
                     (N.TyRcd "m"
                        (N.TyEnvt [N.Type "x" (N.TyRcd "x" (N.TyLit C.TyInt))]))
                 ])

  describe "Elaborate Modules" $ do

    it "elaborates module variable" $ do
      let m = Src.VarM "M"
      let named = elabModule m
      named `shouldBe` Right (N.Var "M")

    -- Modules are sandboxed: every standalone struct / whole functor elaborates
    -- to an empty-environment box ([] ▷ e). A functor's body struct stays unboxed
    -- (it sits inside the functor's box).
    it "elaborates simple struct with let" $ do
      let input = "let x = 1;"
      let parsed = parseModule (lexer input)
      let named = elabModule parsed
      named `shouldBe`
        Right (N.Box [] (N.FEnv [N.ModE "x" (N.Lit (C.LitInt 1))]))

    it "elaborates functor with term argument" $ do
      let m = Src.Functor [("x", Src.TmArgType (Src.TyLit C.TyInt))]
                          (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Right (N.Box [] (N.Lam "x" (N.FEnv [])))

    it "elaborates functor with type argument" $ do
      let m = Src.Functor [("t", Src.TyArg)] (Src.Struct [])
      let named = elabModule m
      named `shouldBe` Right (N.Box [] (N.TLam "t" (N.FEnv [])))

    it "elaborates multi-arg functor to nested" $ do
      let m = Src.Functor [("t", Src.TyArg), ("x", Src.TmArgType (Src.TyVar "t"))]
                          (Src.Struct [])
      let named = elabModule m
      named `shouldBe`
        Right (N.Box [] (N.TLam "t" (N.Lam "x" (N.FEnv []))))

    -- The annotation of a sandboxed module goes inside its box, closed over the
    -- ambient abbreviations: the box body cannot see the ambient context.
    it "places a sandboxed module's annotation inside the box, aliases expanded" $ do
      let input = "module type S = sig val x : int; end; \
                  \module m : S = struct let x : int = 1; end;"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left err -> expectationFailure ("elaboration failed: " ++ err)
        Right (N.Box [] (N.FEnv [N.ModE "m" e, _])) ->
          case e of
            N.Box [] (N.Anno _ t) ->
              t `shouldBe` N.TyEnvt [N.Type "x" (N.TyRcd "x" (N.TyLit C.TyInt))]
            other -> expectationFailure ("unexpected shape: " ++ show other)
        Right other -> expectationFailure ("unexpected shape: " ++ show other)

    it "rejects a sandbox annotation that mentions an outer abstract type" $ do
      let input = "module f = functor (type t) -> struct \
                  \  module inner : sig val v : t; end = struct let v : int = 1; end; \
                  \end;"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left _  -> return ()
        Right _ -> expectationFailure "expected an error about the abstract type"

  describe "Merge elaboration (no core concatenation primitive)" $ do

    -- Composition is expanded at elaboration time into an environment literal
    -- built from projections, so no concatenation node reaches C.
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

    -- The left operand's components come first in the merged environment, so a
    -- type name the right operand's signature mentions from the outside would be
    -- captured by a type component of the left operand.
    it "rejects a merge that would capture a free type name of the right operand" $ do
      let input = "type t = int; \
                  \module m1 : sig type t = bool; val a : bool; end = \
                  \  struct type t = bool; let a : bool = true; end; \
                  \module m2 : sig val f : t -> t; end = \
                  \  struct let f : int -> int = fun (x) -> x; end; \
                  \module r = m1 ++ m2;"
      let parsed = parseModule (lexer input)
      case elabModule parsed of
        Left err -> err `shouldSatisfy` ("captured" `isInfix`)
        Right _  -> expectationFailure "expected a capture error"

    -- Environment entries telescope, so an operand spliced into the merged
    -- environment would have its free variables captured by the other
    -- operand's component names. Operands are projected, never spliced.
    it "does not capture an ambient name with a component of the same name" $ do
      let input = "module f  = struct let z : int = 99; end; \
                  \module m1 : sig val f : int; end = struct let f : int = 1; end; \
                  \module r  = m1 + struct let h : int = (f.z :: int); end; \
                  \let out : int = (r.h :: int);"
      preserves input
      evalTop input `shouldReturn` Just 99

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

    -- Both operands are bound outside every new binder, so a component cannot
    -- shadow the variable operand it came from.
    it "does not let a component shadow the variable operand it came from" $ do
      let input = "module m1 : sig val m1 : int; end = struct let m1 : int = 7; end; \
                  \module m2 : sig val b  : int; end = struct let b  : int = 1; end; \
                  \module r = m1 ++ m2; \
                  \let out : int = (r.m1 :: int);"
      preserves input
      evalTop input `shouldReturn` Just 7

  describe "Type-preserving elaboration (inline programs)" $ do

    it "a struct matched against a signature with a functor member" $ do
      let input = "module type S = sig functor f (type t) (x : t) : sig val v : t; end; end; \
                  \module m : S = struct \
                  \  module f : forall t. t ->m sig val v : t; end = \
                  \    functor (type t) (x) -> struct let v : t = x; end; \
                  \end; \
                  \let out : int = (((m.f @int) :: int -> sig val v : int; end)(3)).v;"
      preserves input
      evalTop input `shouldReturn` Just 3

    it "a module type alias at an elimination site (Typ-teq with Teq-eql)" $ do
      let input = "module type SIG = sig val x : int; end; \
                  \module m : SIG = struct let x : int = 5; end; \
                  \let out : int = m.x;"
      preserves input
      evalTop input `shouldReturn` Just 5

    it "type application of a functor, pinned by a signature ascription" $ do
      let input = "module mk = functor (type e) -> struct let op : list e -> list e = fun (xs) -> take(1, xs); end; \
                  \module ops : sig val op : list int -> list int; end = mk @ int; \
                  \let out : int = length((ops.op :: list int -> list int)(List[1, 2, 3]));"
      preserves input
      evalTop input `shouldReturn` Just 1

    it "a dependent merge of two literal structs with a type dependency" $ do
      let input = "module m = struct type a = int; end + struct type b = a; let y : b = 7; end; \
                  \let out : int = box [mm = m] in (mm.y :: int);"
      preserves input
      evalTop input `shouldReturn` Just 7

  describe "Type-preserving elaboration (examples/*.eml)" $ do
    files <- runIO (sort . filter (".eml" `isSuffixOf`) <$> listDirectory "examples")
    forM_ files $ \f ->
      it f $ do
        src <- readFile ("examples" </> f)
        preserves src

  describe "Documented results of the paper examples" $ do
    it "section24_latest.eml: previewResult = true, mockResult = false" $ do
      src <- readFile ("examples" </> "section24_latest.eml")
      evalLabel "previewResult" src `shouldReturn` Just (C.Lit (C.LitBool True))
      evalLabel "mockResult" src `shouldReturn` Just (C.Lit (C.LitBool False))
    it "section24_dep.eml: previewResult = true, mockResult = false" $ do
      src <- readFile ("examples" </> "section24_dep.eml")
      evalLabel "previewResult" src `shouldReturn` Just (C.Lit (C.LitBool True))
      evalLabel "mockResult" src `shouldReturn` Just (C.Lit (C.LitBool False))
    it "test15.eml: result = List[3, 1]" $ do
      src <- readFile ("examples" </> "test15.eml")
      evalLabel "result" src `shouldReturn`
        Just (C.EList [C.Lit (C.LitInt 3), C.Lit (C.LitInt 1)])
    it "typedep.eml: useY = 7" $ do
      src <- readFile ("examples" </> "typedep.eml")
      evalLabel "useY" src `shouldReturn` Just (C.Lit (C.LitInt 7))

  describe "De Bruijn Conversion" $ do

    it "converts simple lambda" $ do
      let named = N.Lam "x" (N.Var "x")
      let nameless = DB.toDeBruijn named
      nameless `shouldBe` C.Lam (C.Var 0)

    it "converts nested lambda with outer reference" $ do
      let named = N.Lam "x" (N.Lam "y" (N.Var "x"))
      let nameless = DB.toDeBruijn named
      nameless `shouldBe` C.Lam (C.Lam (C.Var 1))

    it "converts type lambda" $ do
      let named = N.TLam "a" (N.Var "x")
      -- Assumes "x" is in context at index 0
      let nameless = DB.toDeBruijn named
      case nameless of
        C.TLam _ -> return ()
        _ -> expectationFailure "Expected TLam"
-- Type preservation: the type claimed by elaboration must be the type the core
-- checker gives the elaborated term (up to type equivalence), and the term must
-- evaluate.

parseModuleTyp' :: String -> Src.ModuleTyp
parseModuleTyp' s =
  case parseTyp (lexer s) of
    Src.TyModule mty -> mty
    other -> error ("not a module type: " ++ show other)

isInfix :: String -> String -> Bool
isInfix needle hay = any (needle `isPrefixOf'`) (suffixes hay)
  where
    suffixes [] = [[]]
    suffixes xs@(_:rest) = xs : suffixes rest
    isPrefixOf' [] _ = True
    isPrefixOf' _ [] = False
    isPrefixOf' (a:as) (b:bs) = a == b && isPrefixOf' as bs

-- | Parse, elaborate, resolve names, type-check and evaluate a program; report
--   the first stage that fails. Returns the elaborated program and its value.
runProgram :: String -> IO (Either String (N.Exp, Maybe N.Typ, C.Typ, C.Exp))
runProgram src = do
  parsedOrErr <- try (evaluate (parseModule (lexer src)))
  case parsedOrErr of
    Left (ex :: SomeException) -> return (Left ("parse error: " ++ show ex))
    Right parsed ->
      case elabModuleExp [] parsed of
        Left err -> return (Left ("elaboration failed: " ++ err))
        Right (e, mt) -> do
          coreOrErr <- try (evaluate (forceExp (DB.toDeBruijn e)))
          case coreOrErr of
            Left (ex :: SomeException) -> return (Left ("name resolution failed: " ++ show ex))
            Right core ->
              case Check.infer [] core of
                Nothing -> return (Left "the elaborated core does not type-check")
                Just t' ->
                  case Eval.eval C.Unit core of
                    Nothing -> return (Left "the elaborated core does not evaluate")
                    Just v  -> return (Right (e, mt, t', v))
  where
    forceExp x = length (show x) `seq` x

preserves :: String -> Expectation
preserves src = do
  r <- runProgram src
  case r of
    Left err -> expectationFailure err
    Right (_, Nothing, _, _) -> return ()
    Right (_, Just t, t', _) ->
      let claimed = DB.toDeBruijnTyp t
      in if Check.teq [] t' claimed []
           then return ()
           else expectationFailure $
                  "claimed type is not equivalent to the checked type\n  claimed: "
                    ++ C.pretty claimed ++ "\n  checked: " ++ C.pretty t'

-- | The value bound to a label of the program's top-level environment.
evalLabel :: String -> String -> IO (Maybe C.Exp)
evalLabel label src = do
  r <- runProgram src
  case r of
    Left err -> expectationFailure err >> return Nothing
    Right (_, _, _, v) -> return (lookupLabel label v)

evalTop :: String -> IO (Maybe Int)
evalTop src = do
  mv <- evalLabel "out" src
  return $ case mv of
    Just (C.Lit (C.LitInt n)) -> Just n
    _ -> Nothing

lookupLabel :: String -> C.Exp -> Maybe C.Exp
lookupLabel label = go
  where
    go (C.Rec l e) | l == label = Just e
                        | otherwise  = Nothing
    go (C.Anno e _) = go e
    go e | Just entries <- C.envEntries e = firstJust (map goE entries)
    go _ = Nothing

    goE (C.EntE e) = go e
    goE (C.EntT _) = Nothing

    firstJust = foldr (\x acc -> maybe acc Just x) Nothing

-- | Does the elaborated program contain an environment literal that merges
--   projections out of two different sources? (A stand-in for "the merge was
--   expanded", since CoreFE has no node to look for.)
hasConcatShape :: N.Exp -> Bool
hasConcatShape = go
  where
    go (N.Box env e)  = any goE env || go e
    go (N.FEnv env)   = any isProj env || any goE env
    go (N.Lam _ e)    = go e
    go (N.TLam _ e)   = go e
    go (N.App a b)    = go a || go b
    go (N.TApp a _)   = go a
    go (N.Anno a _)   = go a
    go (N.Rec _ a)    = go a
    go (N.RProj a _)  = go a
    go _                  = False

    goE (N.ModE _ e) = go e
    goE (N.ExpE _ e) = go e
    goE (N.TypE _ _) = False

    isProj (N.ModE _ (N.RProj _ _)) = True
    isProj _                                = False

-- | Does the elaborated program still reference this source name?
mentionsVar :: String -> N.Exp -> Bool
mentionsVar name = go
  where
    go (N.Var n)      = n == name
    go (N.Box env e)  = any goE env || go e
    go (N.FEnv env)   = any goE env
    go (N.Lam _ e)    = go e
    go (N.TLam _ e)   = go e
    go (N.App a b)    = go a || go b
    go (N.TApp a _)   = go a
    go (N.Anno a _)   = go a
    go (N.Rec _ a)    = go a
    go (N.RProj a _)  = go a
    go _                  = False

    goE (N.ModE _ e) = go e
    goE (N.ExpE _ e) = go e
    goE (N.TypE _ _) = False
