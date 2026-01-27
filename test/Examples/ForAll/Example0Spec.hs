{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}
module Examples.ForAll.Example0Spec where

import qualified CoreForAll.Syntax as C
import Data.Either (isLeft, isRight)
import EnvML.Parser.AST
import EnvML.Parser.Parse (parseEmlFile)
import Test.Hspec

examplePath :: String
examplePath = "examples/ForAll/Example0.eml"

spec :: Spec
spec = do
  describe "Example 0: Basic Modules with Manifest Types" $
    it "parses successfully" $ do
      let envType =
            ModTypE $
              TyModule $
                TySig
                  [ TyDef "t" (TyLit TyInt),
                    ValDecl "inc" (TyArr (TyVar "t") (TyVar "t"))
                  ]

      let envModule =
            ModExpE $
              Anno
                ( ModE $
                    Struct
                      []
                      [ ("t", TypE (TyLit TyInt)),
                        ( "inc",
                          ExpE
                            ( Anno
                                (Lam [("n", TmArg)] (BinOp $ Add (Var "n") (Lit (LitInt 1))))
                                (TyArr (TyVar "t") (TyVar "t"))
                            )
                        )
                      ]
                )
                (TyVar "ENV")

      let resultExpr =
            ExpE $
              Anno
                ( Box
                    [("x", ExpE (Var "env"))]
                    (App (RProj (Var "x") "inc") (Lit (LitInt 10)))
                )
                (TyLit TyInt)

      parseEmlFile examplePath `shouldReturn` Struct [] [("ENV", envType), ("env", envModule), ("result", resultExpr)]

-- it "parses successfully" $ do
-- it "pre-processes (de-bruijn transform + de-sugar) successfully" $ do
-- it "elaborates successfully" $ do
-- it "type checks at core successfully" $ do
-- it "types for elaboration and core match" $ do
-- it "evaluates sucessfully" $ do
-- pure ()

main :: IO ()
main = hspec spec
