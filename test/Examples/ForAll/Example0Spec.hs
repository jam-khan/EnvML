{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}

module Examples.ForAll.Example0Spec where

import qualified Core.Syntax as C
import qualified EnvML.Elab as ElabD
import qualified EnvML.Syntax as D
import qualified EnvML.Parser.AST as N
import Data.Either (isLeft, isRight)
import EnvML.Parse (parseEmlFile)
import Test.Hspec

examplePath :: String
examplePath = "examples/ForAll/Example0.eml"

spec :: Spec
spec = pure ()