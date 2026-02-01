module Examples.ForAll.Example1Spec where

import qualified Core.Syntax as C
import Data.Either (isLeft, isRight)
import qualified EnvML.Elab as ElabD
import qualified EnvML.Parser.AST as N
import EnvML.Parse (parseEmlFile)
import qualified EnvML.Syntax as D
import Test.Hspec

examplePath :: String
examplePath = "examples/ForAll/Example1.eml"

spec :: Spec
spec = pure ()