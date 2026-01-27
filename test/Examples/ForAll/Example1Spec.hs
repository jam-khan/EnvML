module Examples.ForAll.Example1Spec where

import qualified CoreForAll.Syntax as C
import Data.Either (isLeft, isRight)
import EnvML.Parser.AST
import EnvML.Parser.Parse (parseEmlFile)
import Test.Hspec

examplePath :: String
examplePath = "examples/ForAll/Example1.eml"

spec :: Spec
spec = do
  describe "Example 1: Basic Sandboxing" $ do
    let envType =
          TypE (TyAll "t" (TyModule (TySig [ValDecl "id" (TyArr (TyVar "t") (TyVar "t"))])))

    let envModule =
          ModExpE
            ( Anno
                ( ModE
                    ( Functor
                        [("t", TyArg)]
                        ( Struct
                            []
                            [ ( "id",
                                ExpE
                                  ( Anno
                                      (Lam [("x", TmArg)] (Var "x"))
                                      (TyArr (TyVar "t") (TyVar "t"))
                                  )
                              )
                            ]
                        )
                    )
                )
                (TyVar "ENV")
            )

    let intResult =
          ExpE
            ( Anno
                ( Box
                    [("x", ExpE (TApp (Var "env") (TyLit TyInt)))]
                    (App (RProj (Var "x") "id") (Lit (LitInt 1)))
                )
                (TyLit TyInt)
            )

    let boolResult =
          ExpE
            ( Anno
                ( Box
                    [("x", ExpE (TApp (Var "env") (TyLit TyBool)))]
                    (App (RProj (Var "x") "id") (Lit (LitBool True)))
                )
                (TyLit TyBool)
            )

    it "parses successfully" $
      parseEmlFile examplePath
        `shouldReturn` Struct
          []
          [ ("ENV", envType),
            ("env", envModule),
            ("int_result", intResult),
            ("bool_result", boolResult)
          ]
    -- it "parses successfully" $ do
    -- it "pre-processes (de-bruijn transform + de-sugar) successfully" $ do
    -- it "elaborates successfully" $ do
    -- it "type checks at core successfully" $ do
    -- it "types for elaboration and core match" $ do
    -- it "evaluates sucessfully" $ do
    pure ()

main :: IO ()
main = hspec spec
