{-# LANGUAGE ScopedTypeVariables #-}
module EnvML.CheckSpec (spec) where

import EnvML.Syntax (Name, Typ(..), TyCtxE(..), TyCtx, ModuleTyp(..), FunArg(..), Intf, IntfE(..))
import qualified EnvML.Desugared as D
import EnvML.Desugar (desugarExp, desugarModule)
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import EnvML.Check
import qualified CoreFE.Syntax as CoreFE
import Data.Maybe (isJust)
import Test.Hspec
import Debug.Trace (trace)

pe :: String -> D.Exp
pe input = desugarExp (parseExp (lexer input))

pt :: String -> Typ
pt input = parseTyp (lexer input)

-- Helper: parse a module, desugar, and infer its structures
inferMod' :: String -> Maybe Intf
inferMod' input =
  let m = desugarModule (parseModule (lexer input))
  in case m of
    D.Struct structs -> inferStructs [] structs
    _ -> Nothing

spec :: Spec
spec = do
  describe "infer literals" $ do
    it "infers int literal" $
      infer [] (pe "42") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "infers bool literal true" $
      infer [] (pe "true") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers bool literal false" $
      infer [] (pe "false") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers string literal" $
      infer [] (pe "\"hello\"") `shouldBe` Just (TyLit CoreFE.TyStr)

    it "infers unit literal" $
      infer [] (pe "()") `shouldBe` Just (TyLit CoreFE.TyUnit)

  describe "infer variables" $ do
    it "infers variable from context" $
      infer [TypeN "x" (TyLit CoreFE.TyInt)] (pe "x")
        `shouldBe` Just (TyLit CoreFE.TyInt)

    it "fails for unbound variable" $
      infer [] (pe "x") `shouldBe` Nothing

  describe "infer applications" $ do
    it "infers simple function application" $
      let ctx = [TypeN "f" (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool)),
                 TypeN "x" (TyLit CoreFE.TyInt)]
      in infer ctx (pe "f(x)") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "fails application with wrong argument type" $
      let ctx = [TypeN "f" (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool)),
                 TypeN "x" (TyLit CoreFE.TyBool)]
      in infer ctx (pe "f(x)") `shouldBe` Nothing

  describe "infer type application" $ do
    it "infers type application" $
      let ctx = [TypeN "id" (TyAll "a" (TyArr (TyVar "a") (TyVar "a")))]
      in infer ctx (pe "id @ int") `shouldBe`
           Just (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))

  describe "infer if expressions" $ do
    it "infers if expression" $
      infer [] (pe "if true then 1 else 0")
        `shouldBe` Just (TyLit CoreFE.TyInt)

    it "fails if with non-bool condition" $
      let ctx = [TypeN "x" (TyLit CoreFE.TyInt)]
      in infer ctx (pe "if x then 1 else 0") `shouldBe` Nothing

    it "fails if with mismatched branches" $
      infer [] (pe "if true then 1 else false") `shouldBe` Nothing

  describe "infer binary ops" $ do
    it "infers addition" $
      infer [] (pe "1 + 2") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "infers subtraction" $
      infer [] (pe "1 - 2") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "infers multiplication" $
      infer [] (pe "2 * 3") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "infers equality comparison" $
      infer [] (pe "1 == 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers inequality comparison" $
      infer [] (pe "1 != 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers less than" $
      infer [] (pe "1 < 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers less equal" $
      infer [] (pe "1 <= 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers greater than" $
      infer [] (pe "1 > 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers greater equal" $
      infer [] (pe "1 >= 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "fails addition with bool" $
      let ctx = [TypeN "x" (TyLit CoreFE.TyBool)]
      in infer ctx (pe "x + 1") `shouldBe` Nothing

  describe "infer records" $ do
    it "infers empty record" $
      infer [] (pe "{}") `shouldBe` Just (TyRcd [])

    it "infers record with fields" $
      infer [] (pe "{x = 1, y = true}")
        `shouldBe` Just (TyRcd [("x", TyLit CoreFE.TyInt), ("y", TyLit CoreFE.TyBool)])

    it "infers record projection" $
      let ctx = [TypeN "r" (TyRcd [("x", TyLit CoreFE.TyInt), ("y", TyLit CoreFE.TyBool)])]
      in infer ctx (pe "r.x") `shouldBe` Just (TyLit CoreFE.TyInt)

  describe "infer fenv" $ do
    it "infers empty fenv" $
      infer [] (D.FEnv []) `shouldBe` Just (TyCtx [])

    it "infers fenv with named expression" $
      infer [] (D.FEnv [D.ExpEN "x" (D.Lit (CoreFE.LitInt 1))])
        `shouldBe` Just (TyCtx [TypeN "x" (TyLit CoreFE.TyInt)])

    it "infers fenv with multiple named expressions" $
      infer [] (D.FEnv [D.ExpEN "x" (D.Lit (CoreFE.LitInt 1)),
                         D.ExpEN "y" (D.Lit (CoreFE.LitBool True))])
        `shouldBe` Just (TyCtx [TypeN "x" (TyLit CoreFE.TyInt),
                                 TypeN "y" (TyLit CoreFE.TyBool)])

    it "infers fenv with named type" $
      infer [] (D.FEnv [D.TypEN "t" (TyLit CoreFE.TyInt)])
        `shouldBe` Just (TyCtx [TypeN "t" (TyLit CoreFE.TyInt)])

    it "infers fenv where later entry references earlier" $
      infer [] (D.FEnv [D.ExpEN "y" (D.Var "x"),
                         D.ExpEN "x" (D.Lit (CoreFE.LitInt 42))])
        `shouldBe` Just (TyCtx [TypeN "y" (TyLit CoreFE.TyInt),
                                 TypeN "x" (TyLit CoreFE.TyInt)])

    it "fails fenv with unbound variable" $
      infer [] (D.FEnv [D.ExpEN "x" (D.Var "z")])
        `shouldBe` Nothing

  describe "infer annotations" $ do
    it "infers annotated expression" $
      infer [] (pe "(1 :: int)") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "fails annotation with wrong type" $
      infer [] (pe "(1 :: bool)") `shouldBe` Nothing

  describe "infer lists" $ do
    it "infers non-empty list" $
      infer [] (pe "List[1, 2, 3]") `shouldBe` Just (TyList (TyLit CoreFE.TyInt))

    it "fails empty list (no type info)" $
      infer [] (pe "List[]") `shouldBe` Nothing

    it "fails list with mixed types" $
      infer [] (pe "List[1, true]") `shouldBe` Nothing

  describe "check lambda" $ do
    it "checks simple lambda" $
      check [] (pe "fun (x : int) -> x") (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` True

    it "checks lambda with unannotated arg" $
      check [] (pe "fun (x) -> x") (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` True

    it "checks type lambda" $
      check [] (pe "fun (type a) -> 2") (TyAll "a" (TyLit CoreFE.TyInt))
        `shouldBe` True

    it "rejects lambda with wrong return type" $
      check [] (pe "fun (x : int) -> true") (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` False

    it "rejects lambda when TmArgType annotation mismatches checked arrow domain" $
      check [] (pe "fun (x : bool) -> x") (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` False

    it "accepts lambda when TmArgType annotation matches checked arrow domain" $
      check [] (pe "fun (x : int) -> x") (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` True

  describe "check fix" $ do
    it "checks fixpoint" $
      check [] (pe "fix f. fun (x : int) -> f(x)")
        (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` True

  describe "check lists" $ do
    it "checks non-empty list" $
      check [] (pe "List[1, 2]") (TyList (TyLit CoreFE.TyInt)) `shouldBe` True

    it "rejects list with wrong element type" $
      check [] (pe "List[true]") (TyList (TyLit CoreFE.TyInt)) `shouldBe` False

  describe "teq type equality" $ do
    it "teq for identical base types" $
      teq [] (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt) [] `shouldBe` True

    it "teq for different base types" $
      teq [] (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool) [] `shouldBe` False

    it "teq for arrow types" $
      teq [] (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool))
             (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool)) []
        `shouldBe` True

    it "teq resolves type aliases" $
      teq [TypeEqN "t" (TyLit CoreFE.TyInt)] (TyVar "t") (TyLit CoreFE.TyInt) []
        `shouldBe` True

    it "teq for forall types" $
      teq [] (TyAll "a" (TyVar "a")) (TyAll "b" (TyVar "b")) []
        `shouldBe` True

    it "teq for mu types" $
      teq [] (TyMu "a" (TyVar "a")) (TyMu "b" (TyVar "b")) []
        `shouldBe` True

    it "teq TyBoxT on left equals inner type with concrete ctx" $
      let ctx = [TypeN "x" (TyLit CoreFE.TyInt)]
      in teq [] (TyBoxT ctx (TyLit CoreFE.TyInt)) (TyLit CoreFE.TyInt) []
        `shouldBe` True

    it "teq TyBoxT on right equals inner type with concrete ctx" $
      let ctx = [TypeN "x" (TyLit CoreFE.TyInt)]
      in teq [] (TyLit CoreFE.TyInt) (TyBoxT ctx (TyLit CoreFE.TyInt)) []
        `shouldBe` True

    it "teq TyBoxT fails with non-concrete ctx" $
      let ctx = [KindN "a"]
      in teq [] (TyBoxT ctx (TyVar "a")) (TyLit CoreFE.TyInt) []
        `shouldBe` False

    it "teq TyBoxT resolves names from box ctx" $
      let ctx = [TypeEqN "t" (TyLit CoreFE.TyInt)]
      in teq [] (TyBoxT ctx (TyVar "t")) (TyLit CoreFE.TyInt) []
        `shouldBe` True

    it "teq TyModule equality" $
      let mty = TySig [ValDecl "x" (TyLit CoreFE.TyInt)]
      in teq [] (TyModule mty) (TyModule mty) []
        `shouldBe` True

  describe "infer fold/unfold (desugared)" $ do
    it "infers fold with TyMu type" $
      let ty = TyMu "X" (TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)])
          ctx = []
      in infer ctx (D.Fold ty (D.DataCon "Nil" (D.Lit CoreFE.LitUnit) (typeSubstName "X" ty (TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]))))
        `shouldBe` Just ty

    it "infers unfold returns unfolded type" $
      let ty = TyMu "X" (TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)])
          ctx = [TypeN "x" ty]
      in infer ctx (D.Unfold (D.Var "x"))
        `shouldBe` Just (typeSubstName "X" ty (TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]))

  describe "infer case (desugared)" $ do
    it "infers case expression on sum type" $
      let sumTy = TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]
          ctx = [TypeN "x" sumTy]
      in infer ctx (D.Case (D.Var "x") [D.CaseBranch "Nil" "u" (D.Lit (CoreFE.LitInt 0)),
                                          D.CaseBranch "Cons" "n" (D.Var "n")])
        `shouldBe` Just (TyLit CoreFE.TyInt)

  describe "infer DataCon (check mode)" $ do
    it "checks DataCon against sum type" $
      let sumTy = TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]
      in check [] (D.DataCon "Nil" (D.Lit CoreFE.LitUnit) sumTy) sumTy
        `shouldBe` True

    it "rejects DataCon with wrong payload" $
      let sumTy = TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]
      in check [] (D.DataCon "Nil" (D.Lit (CoreFE.LitInt 1)) sumTy) sumTy
        `shouldBe` False

  describe "infer modules" $ do
    it "infers simple struct module" $
        inferMod' "type t = int; let x : t = 1;"
            `shouldBe` Just
            [ TyDef "t" (TyLit CoreFE.TyInt)
            , ValDecl "x" (TyVar "t")
            ]

    it "infers struct with multiple lets" $
      inferMod' "let x : int = 1; let y : bool = true;"
        `shouldBe` Just [ValDecl "x" (TyLit CoreFE.TyInt),
                         ValDecl "y" (TyLit CoreFE.TyBool)]

    it "infers let with type alias usage" $
      inferMod' "type t = int; let x : t = 1;"
        `shouldBe` Just [TyDef "t" (TyLit CoreFE.TyInt),
                         ValDecl "x" (TyVar "t")]

  describe "checkMod" $ do
    it "checks struct against sig" $
      let m = desugarModule (parseModule (lexer "type t = int; let x : t = 1;"))
          mty = TySig [TyDef "t" (TyLit CoreFE.TyInt),
                        ValDecl "x" (TyVar "t")]
      in checkMod [] m mty `shouldBe` True

    it "checks functor against arrow module type" $
      let m = desugarModule (parseModule (lexer "module m = functor (x : int) -> struct let y : int = x; end;"))
          mty = TyArrowM (TyLit CoreFE.TyInt)
                          (TySig [ValDecl "y" (TyLit CoreFE.TyInt)])
      in case m of
        D.Struct [D.ModStruct _ _ fm] -> checkMod [] fm mty `shouldBe` True
        _ -> expectationFailure "Expected ModStruct"

    it "checks functor with type arg against ForallM" $
      let m = desugarModule (parseModule (lexer "module m = functor (type a) -> struct let id : a -> a = fun (x) -> x; end;"))
          mty = ForallM "a" (TySig [ValDecl "id" (TyArr (TyVar "a") (TyVar "a"))])
      in case m of
        D.Struct [D.ModStruct _ _ fm] -> checkMod [] fm mty `shouldBe` True
        _ -> expectationFailure "Expected ModStruct"

    it "rejects functor when TmArgType annotation mismatches checked arrow domain" $
      let m = desugarModule (parseModule (lexer "module m = functor (x : bool) -> struct end;"))
          mty = TyArrowM (TyLit CoreFE.TyInt) (TySig [])
      in case m of
        D.Struct [D.ModStruct _ _ fm] -> checkMod [] fm mty `shouldBe` False
        _ -> expectationFailure "Expected ModStruct"

    it "accepts functor when TmArgType annotation matches checked arrow domain" $
      let m = desugarModule (parseModule (lexer "module m = functor (x : int) -> struct end;"))
          mty = TyArrowM (TyLit CoreFE.TyInt) (TySig [])
      in case m of
        D.Struct [D.ModStruct _ _ fm] -> checkMod [] fm mty `shouldBe` True
        _ -> expectationFailure "Expected ModStruct"

    it "accepts functor with unannotated TmArg against arrow module type" $
      let m = desugarModule (parseModule (lexer "module m = functor (x) -> struct end;"))
          mty = TyArrowM (TyLit CoreFE.TyInt) (TySig [])
      in case m of
        D.Struct [D.ModStruct _ _ fm] -> checkMod [] fm mty `shouldBe` True
        _ -> expectationFailure "Expected ModStruct"

  describe "full module type checking (parsed)" $ do
    it "infers simple module" $ do
      let input = "let x : int = 42;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs
          `shouldBe` Just [ValDecl "x" (TyLit CoreFE.TyInt)]
        _ -> expectationFailure "Expected Struct"

    it "infers module with type decl" $ do
      let input = "type t = int; let x : t = 42;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs
          `shouldBe` Just [TyDef "t" (TyLit CoreFE.TyInt),
                           ValDecl "x" (TyVar "t")]
        _ -> expectationFailure "Expected Struct"

    it "infers module with function" $ do
      let input = "let f : int -> int = fun (x : int) -> x;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs
          `shouldBe` Just [ValDecl "f" (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))]
        _ -> expectationFailure "Expected Struct"

    it "infers annotated module" $ do
      let input = "module m : sig type t = int; val y : t; end = struct type t = int; let y : t = 10; end;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

    it "infers polymorphic identity functor" $ do
      let input = unlines
            [ "module type POLICY = forallm t. sig val trans : t -> t; end;"
            , "module policy1 : POLICY = functor (type t) -> struct let trans : t -> t = fun (x) -> x; end;"
            ]
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

    it "infers module type application (@m)" $ do
      let input = unlines
            [ "module policy1 = functor (type t) -> struct let id : t -> t = fun (x) -> x; end;"
            , "module result = policy1 @m int;"
            ]
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

    it "infers module annotation (::m)" $ do
      let input = unlines
            [ "module policy1 = functor (type t) -> struct let id : t -> t = fun (x) -> x; end;"
            , "module result = policy1 @m int ::m sig val id : int -> int; end;"
            ]
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

    it "infers module projection from sig with type def" $ do
      let input = "let f : int -> int = (struct type a = int; let id : a -> a = fun (x) -> x; end ::m sig type a = int; val id : a -> a; end).id;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

    it "infers functor with module-typed arg (->m)" $ do
      let input = unlines
            [ "module type POLICY = forallm t. sig val trans : t -> t; end;"
            , "module foo : (forallm t. sig val trans : t -> t; end) ->m sig type a = int; val f : a -> a; end"
            , "  = functor (m) -> struct type a = int;"
            , "      let f : a -> a = ((m @m a) ::m sig val trans : int -> int; end).trans; end;"
            ]
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

    it "infers module application (|...|)" $ do
      let input = unlines
            [ "module type POLICY = forallm t. sig val trans : t -> t; end;"
            , "module policy1 : POLICY = functor (type t) -> struct let trans : t -> t = fun (x) -> x; end;"
            , "module foo : (forallm t. sig val trans : t -> t; end) ->m sig type a = int; val f : a -> a; end"
            , "  = functor (m) -> struct type a = int;"
            , "      let f : a -> a = ((m @m a) ::m sig val trans : int -> int; end).trans; end;"
            , "let result : int = box [impl = foo(|policy1|)] in (impl.f :: int -> int)(42);"
            ]
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

    it "rejects module annotation with wrong sig" $ do
      let input = unlines
            [ "module policy1 = functor (type t) -> struct let id : t -> t = fun (x) -> x; end;"
            , "module result = policy1 @m int ::m sig val id : bool -> bool; end;"
            ]
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldBe` Nothing
        _ -> expectationFailure "Expected Struct"

    it "rejects functor checked against wrong ForallM sig" $ do
      let m = desugarModule (parseModule (lexer "module m = functor (type a) -> struct let id : a -> a = fun (x) -> x; end;"))
          mty = ForallM "a" (TySig [ValDecl "id" (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))])
      case m of
        D.Struct [D.ModStruct _ _ fm] -> checkMod [] fm mty `shouldBe` False
        _ -> expectationFailure "Expected ModStruct"

    it "infers full ACCESS_POLICY example (test12)" $ do
      let input = unlines
            [ "module type ACCESS_POLICY = forallm t. sig val reshape : list t -> list t; end;"
            , "module previewPolicy : ACCESS_POLICY = functor (type t) -> struct let reshape : list t -> list t = fun (ls) -> take(2, ls); end;"
            , "module mockPolicy : ACCESS_POLICY = functor (type t) -> struct let reshape : list t -> list t = fun (ls) -> ls; end;"
            , "module queryProcessor : (forallm t. sig val reshape : list t -> list t; end) ->m sig type a = int; val query : list a -> list a; end"
            , "  = functor (policy) -> struct type a = int;"
            , "      let query : list a -> list a = ((policy @m a) ::m sig val reshape : list int -> list int; end).reshape; end;"
            , "let executeQuery : sig type a = int; val query : list a -> list a; end -> list int ="
            , "  fun (processor) -> box [proc = processor] in proc.query(List[3, 1, 2]) :: list int;"
            , "let previewResult : list int = executeQuery(queryProcessor(|previewPolicy|));"
            , "let mockResult : list int = executeQuery(queryProcessor(|mockPolicy|));"
            ]
      let m = desugarModule (parseModule (lexer input))
      case m of
        D.Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"
