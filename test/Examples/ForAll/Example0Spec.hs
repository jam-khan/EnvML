module Examples.ForAll.Example0Spec where


import qualified CoreForAll.Syntax as C
import Data.Either (isLeft, isRight)
import EnvML.Parser.AST
import Test.Hspec
import EnvML.Parser.Parse (parseEmlFile)


examplePath :: String
examplePath = "examples/ForAll/Example0.eml"

spec :: Spec
spec = do
  describe "Example 0: Basic Modules with Manifest Types" $ 
    it "parses successfully" $
      parseEmlFile examplePath `shouldReturn` (Struct [] [("x", ExpE $ Lit (LitInt 1))])
    -- it "parses successfully" $ do
    -- it "pre-processes (de-bruijn transform + de-sugar) successfully" $ do
    -- it "elaborates successfully" $ do
    -- it "type checks at core successfully" $ do
    -- it "types for elaboration and core match" $ do
    -- it "evaluates sucessfully" $ do
    -- pure ()

main :: IO ()
main = hspec spec
