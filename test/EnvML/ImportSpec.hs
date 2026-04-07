{-# LANGUAGE ScopedTypeVariables #-}
module EnvML.ImportSpec (spec) where

import EnvML.Syntax (Name, ModuleTyp(..), Intf, IntfE(..), Typ(..), FunArg(..))
import qualified CoreFE.Syntax as CoreFE
import qualified EnvML.Desugared as D
import EnvML.Desugar (desugarModuleWithImports, desugarModuleTyp)
import EnvML.Desugar (resolveImports)
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseModule, parseModuleTyp)
import Control.Exception (evaluate, SomeException, try)
import Data.Maybe (isJust)
import Test.Hspec

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

pm :: String -> D.Module
pm input = desugarModuleWithImports [] (parseModule (lexer input))

pmt :: String -> ModuleTyp
pmt input = parseModuleTyp (lexer input)

-- | Parse a module string and apply importTypes via desugarModuleWithImports.
pmWith :: [(Name, ModuleTyp)] -> String -> D.Module
pmWith importTypes input =
  desugarModuleWithImports importTypes (parseModule (lexer input))

-- | Path helpers for example import files (relative to project root)
singleImportFile :: FilePath
singleImportFile = "examples/sepcomptest_0/main.eml"

multiImportFile :: FilePath
multiImportFile = "examples/sepcomptest_1/main.eml"

-- ---------------------------------------------------------------------------
-- Spec
-- ---------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Import parsing" $ do

    it "parses a single import statement without error" $ do
      let m = parseModule (lexer "import Foo;")
      show m `shouldContain` "Import"

    it "parses multiple import statements" $ do
      let m = parseModule (lexer "import Foo;\nimport Bar;")
      let src = show m
      src `shouldContain` "\"Foo\""
      src `shouldContain` "\"Bar\""

    it "imports can appear before other definitions" $ do
      let m = parseModule (lexer "import M;\nlet x : int = 1;")
      show m `shouldContain` "Import"

  describe "desugarModuleWithImports – no imports" $ do

    it "desugars a struct without imports unchanged" $ do
      let m = pmWith [] "let x : int = 1;"
      case m of
        D.Struct [D.Let "x" _ _] -> return ()
        _ -> expectationFailure $ "Expected Struct [Let], got: " ++ show m

    it "desugars multiple bindings without imports" $ do
      let m = pmWith [] "let x : int = 1;\nlet y : int = 2;"
      case m of
        D.Struct structs -> length structs `shouldBe` 2
        _ -> expectationFailure $ "Expected Struct, got: " ++ show m

  describe "desugarModuleWithImports – single import" $ do

    let mathSig :: ModuleTyp
        mathSig = pmt "val add : int -> int -> int;\nval square : int -> int;"

    it "wraps body in a single functor for one import" $ do
      let m = pmWith [("math", mathSig)]
                     "import math;\nlet r : int = math.square(3);"
      case m of
        D.Functor "math" _ (D.Struct _) -> return ()
        _ -> expectationFailure $ "Expected Functor math -> Struct, got: " ++ show m

    it "functor argument has TmArgType (sig ...)" $ do
      let m = pmWith [("math", mathSig)]
                     "import math;\nlet r : int = math.square(3);"
      case m of
        D.Functor _ (TmArgType (TyModule (TySig _))) _ -> return ()
        _ -> expectationFailure $
               "Expected TmArgType (TyModule (TySig _)), got: " ++ show m

    it "body struct contains the let binding" $ do
      let m = pmWith [("math", mathSig)]
                     "import math;\nlet r : int = math.square(3);"
      case m of
        D.Functor _ _ (D.Struct structs) ->
          length structs `shouldBe` 1
        _ -> expectationFailure $ "Expected Functor -> Struct, got: " ++ show m

  describe "desugarModuleWithImports – multiple imports" $ do

    let mathSig :: ModuleTyp
        mathSig = pmt "val add : int -> int -> int;\nval square : int -> int;"

        utilsSig :: ModuleTyp
        utilsSig = pmt "val greet : int -> int;\nval version : int;"

    it "wraps body in nested functors (outermost = first import)" $ do
      let m = pmWith [("math", mathSig), ("utils", utilsSig)]
                     "import math;\nimport utils;\nlet r : int = 1;"
      case m of
        D.Functor "math" _ (D.Functor "utils" _ (D.Struct _)) -> return ()
        _ -> expectationFailure $
               "Expected Functor math -> Functor utils -> Struct, got: " ++ show m

    it "fails with error when import has no matching emli entry" $ do
      result <- (try $ evaluate $ length $ show $
        pmWith [("math", mathSig)]      -- utils is missing
               "import math;\nimport utils;\nlet r : int = 1;") :: IO (Either SomeException Int)
      case result of
        Left _ -> return ()     -- expected: error thrown
        Right _ -> expectationFailure "Expected an error for missing .emli, but got success"

  describe "resolveImports – single_import.eml" $ do

    it "loads and parses the single-import example" $ do
      m <- resolveImports singleImportFile
      case m of
        D.MAnno (D.Functor "math" _ (D.Struct _)) _ -> return ()
        _ -> expectationFailure $
               "Expected MAnno (Functor math -> Struct) _, got: " ++ show m

    it "functor type comes from math.emli" $ do
      m <- resolveImports singleImportFile
      case m of
        D.MAnno (D.Functor _ (TmArgType (TyModule (TySig intf))) _) _ -> do
          let names = [n | ValDecl n _ <- intf]
          names `shouldSatisfy` ("add" `elem`)
          names `shouldSatisfy` ("square" `elem`)
        _ -> expectationFailure $
               "Expected MAnno (functor with TySig from math.emli) _, got: " ++ show m

    it "annotation type has import arg as TyArrowM" $ do
      m <- resolveImports singleImportFile
      case m of
        D.MAnno _ (TyArrowM (TyModule (TySig _)) (TySig _)) -> return ()
        _ -> expectationFailure $
               "Expected annotation TyArrowM (TyModule (TySig _)) (TySig _), got: " ++ show m

  describe "resolveImports – multi_import.eml" $ do

    it "loads and parses the multi-import example" $ do
      m <- resolveImports multiImportFile
      case m of
        D.MAnno (D.Functor "math" _ (D.Functor "utils" _ (D.Struct _))) _ -> return ()
        _ -> expectationFailure $
               "Expected MAnno (Functor math -> Functor utils -> Struct) _, got: " ++ show m

    it "body struct has all three let bindings" $ do
      m <- resolveImports multiImportFile
      case m of
        D.MAnno (D.Functor _ _ (D.Functor _ _ (D.Struct structs))) _ ->
          length structs `shouldBe` 3
        _ -> expectationFailure $
               "Expected MAnno (nested functors wrapping 3 bindings) _, got: " ++ show m

    it "annotation type chains import sigs then main sig" $ do
      m <- resolveImports multiImportFile
      case m of
        D.MAnno _ (TyArrowM (TyModule (TySig _)) (TyArrowM (TyModule (TySig _)) (TySig _))) -> return ()
        _ -> expectationFailure $
               "Expected annotation TyArrowM _ (TyArrowM _ (TySig _)), got: " ++ show m

    it "wraps a TySum in TyDef with TyMu" $ do
      let raw = TySig [TyDef "Color" (TySum [("Red", TyLit CoreFE.TyInt), ("Blue", TyLit CoreFE.TyInt)])]
          desugared = desugarModuleTyp raw
      case desugared of
        TySig [TyDef "Color" (TyMu "Color" (TySum _))] -> return ()
        _ -> expectationFailure $ "Expected TyDef Color (TyMu Color (TySum _)), got: " ++ show desugared

    it "leaves non-sum TyDef entries unchanged" $ do
      let raw = TySig [TyDef "MyInt" (TyVar "int")]
          desugared = desugarModuleTyp raw
      desugared `shouldBe` TySig [TyDef "MyInt" (TyVar "int")]

    it "desugars ValDecl types including those referencing the sum type" $ do
      let raw = TySig [ TyDef "Color" (TySum [("Red", TyLit CoreFE.TyInt)])
                      , ValDecl "paint" (TySum [("Red", TyLit CoreFE.TyInt)]) ]
          desugared = desugarModuleTyp raw
      case desugared of
        TySig [TyDef "Color" (TyMu "Color" _), ValDecl "paint" (TySum _)] -> return ()
        _ -> expectationFailure $ "Unexpected: " ++ show desugared

    it "recurses into TyArrowM argument types" $ do
      let innerSig = TySig [TyDef "Shape" (TySum [("Circle", TyLit CoreFE.TyInt)])]
          raw = TyArrowM (TyModule innerSig) (TySig [ValDecl "x" (TyLit CoreFE.TyInt)])
          desugared = desugarModuleTyp raw
      case desugared of
        TyArrowM (TyModule (TySig [TyDef "Shape" (TyMu "Shape" _)])) _ -> return ()
        _ -> expectationFailure $ "Expected TyArrowM with desugared inner sig, got: " ++ show desugared

    it "recurses into nested TyModule inside ValDecl" $ do
      let innerSig = TySig [TyDef "T" (TySum [("A", TyLit CoreFE.TyInt)])]
          raw = TySig [ValDecl "m" (TyModule innerSig)]
          desugared = desugarModuleTyp raw
      case desugared of
        TySig [ValDecl "m" (TyModule (TySig [TyDef "T" (TyMu "T" _)]))] -> return ()
        _ -> expectationFailure $ "Expected nested TyMu inside ValDecl TyModule, got: " ++ show desugared
