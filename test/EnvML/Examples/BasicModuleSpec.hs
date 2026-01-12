module EnvML.Examples.BasicModuleSpec (spec) where

import Test.Hspec
import EnvML.Parser.Parse
import EnvML.Parser.AST

shouldParseAs :: IO Module -> Module -> Expectation
shouldParseAs action expected = action `shouldReturn` expected

shouldParseSigAs :: IO ModuleTyp -> ModuleTyp -> Expectation
shouldParseSigAs action expected = action `shouldReturn` expected

spec :: Spec
spec = describe "Feature: Basic Modules" $ do

  it "parses x.eml" $ 
    parseEmlFile "examples/basic-module/x.eml" `shouldParseAs` Struct 
      [ ("x", ExpE (Lit (LitInt 1)))
      ]

  it "parses x.emli" $ 
    parseEmliFile "examples/basic-module/x.emli" `shouldParseSigAs` TySig 
      [ ValDecl "x" (TyLit TyInt)
      ]