module Examples.ForAll.Example2Spec where

import qualified Core.Syntax as C
import Data.Either (isLeft, isRight)
import EnvML.Parser.AST
import Test.Hspec
import EnvML.Parse (parseEmlFile)


examplePath :: String
examplePath = "examples/ForAll/Example2.eml"

spec :: Spec
spec = do
  describe "Example 2: Sandboxing with polymorphic context" $ do
    xit "parses successfully" $
      parseEmlFile examplePath `shouldReturn` (Struct [] [])
    -- it "parses successfully" $ do
    -- it "pre-processes (de-bruijn transform + de-sugar) successfully" $ do
    -- it "elaborates successfully" $ do
    -- it "type checks at core successfully" $ do
    -- it "types for elaboration and core match" $ do
    -- it "evaluates sucessfully" $ do
    pure ()

