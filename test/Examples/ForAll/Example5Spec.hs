module Examples.ForAll.Example5Spec where

import qualified Core.Syntax as C
import Data.Either (isLeft, isRight)
import EnvML.Parser.AST
import Test.Hspec
import EnvML.Parse (parseEmlFile)


examplePath :: String
examplePath = "examples/ForAll/Example4.eml"

spec :: Spec
spec = pure ()
-- spec = do
--   describe "Example 5: Contextual Polymorphism with first-class modules with polymorphic getter" $ do
--     it "parses successfully" $
--       parseEmlFile examplePath `shouldReturn` (Struct [] [])
--     -- it "pre-processes (de-bruijn transform + de-sugar) successfully" $ do
--     -- it "elaborates successfully" $ do
--     -- it "type checks at core successfully" $ do
--     -- it "types for elaboration and core match" $ do
--     -- it "evaluates sucessfully" $ do
--     pure ()

-- main :: IO ()
-- main = hspec spec
