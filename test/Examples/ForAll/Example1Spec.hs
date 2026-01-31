module Examples.ForAll.Example1Spec where

import qualified Core.Syntax as C
import Data.Either (isLeft, isRight)
import qualified EnvML.Elab as ElabD
import qualified EnvML.Parser.AST as N
import qualified EnvML.Parser.ElabAST as ElabN
import EnvML.Parser.Parse (parseEmlFile)
import qualified EnvML.Syntax as D
import Test.Hspec

examplePath :: String
examplePath = "examples/ForAll/Example1.eml"

spec :: Spec
spec = do
  parsedData <- runIO $ parseEmlFile examplePath
  describe "Example 1: Basic Sandboxing" $ do
    it "parses successfully" $ do
      parsedData `shouldBe` expectedAst

    it "pre-processes (de-bruijn transform + de-sugar) successfully" $ do
      let astElabExpr = ElabN.elabModule [] parsedData
      astElabExpr `shouldBe` expectedEnvMLExpr

    it "elaborates successfully" $ do
      let envMLElabExpr = ElabD.elabM expectedEnvMLExpr
      envMLElabExpr `shouldBe` Right expectedCoreExpr
  where
    -- it "type checks at core successfully" $ do
    -- it "types for elaboration and core match" $ do
    -- it "evaluates successfully" $ do

    expectedAst =
      N.Struct
        []
        [ ("ENV", envType),
          ("env", envModule),
          ("int_result", intResult),
          ("bool_result", boolResult)
        ]
      where
        envType =
          N.TypE (N.TyAll "t" (N.TyModule (N.TySig [N.ValDecl "id" (N.TyArr (N.TyVar "t") (N.TyVar "t"))])))

        envModule =
          N.ModExpE
            ( N.Anno
                ( N.ModE
                    ( N.Functor
                        [("t", N.TyArg)]
                        ( N.Struct
                            []
                            [ ( "id",
                                N.ExpE
                                  ( N.Anno
                                      (N.Lam [("x", N.TmArg)] (N.Var "x"))
                                      (N.TyArr (N.TyVar "t") (N.TyVar "t"))
                                  )
                              )
                            ]
                        )
                    )
                )
                (N.TyVar "ENV")
            )

        intResult =
          N.ExpE
            ( N.Anno
                ( N.Box
                    [("x", N.ExpE (N.TApp (N.Var "env") (N.TyLit N.TyInt)))]
                    (N.App (N.RProj (N.Var "x") "id") (N.Lit (N.LitInt 1)))
                )
                (N.TyLit N.TyInt)
            )

        boolResult =
          N.ExpE
            ( N.Anno
                ( N.Box
                    [("x", N.ExpE (N.TApp (N.Var "env") (N.TyLit N.TyBool)))]
                    (N.App (N.RProj (N.Var "x") "id") (N.Lit (N.LitBool True)))
                )
                (N.TyLit N.TyBool)
            )

    expectedEnvMLExpr =
      D.Struct
        [ boolResult,
          intResult,
          envModule,
          envType
        ]
      where
        envType = D.TypE (D.TyAll (D.TyModule (D.TySig [D.ValDecl (D.TyArr (D.TyVar 0) (D.TyVar 0))])))

        envModule =
          D.ModExpE
            ( D.Anno
                ( D.ModE
                    ( D.Functort
                        ( D.Struct
                            [ D.ExpE
                                ( D.Anno
                                    (D.Lam (D.Var 0))
                                    (D.TyArr (D.TyVar 0) (D.TyVar 0))
                                )
                            ]
                        )
                    )
                )
                (D.TyVar 0)
            )

        intResult =
          D.ExpE
            ( D.Anno
                ( D.Box
                    [D.ExpE (D.TApp (D.Var 0) (D.TyLit D.TyInt))]
                    (D.App (D.RProj (D.Var 0) "id") (D.Lit (D.LitInt 1)))
                )
                (D.TyLit D.TyInt)
            )

        boolResult =
          D.ExpE
            ( D.Anno
                ( D.Box
                    [D.ExpE (D.TApp (D.Var 1) (D.TyLit D.TyBool))]
                    (D.App (D.RProj (D.Var 0) "id") (D.Lit (D.LitBool True)))
                )
                (D.TyLit D.TyBool)
            )

    expectedCoreExpr =
      C.FEnv
        [ boolResult,
          intResult,
          envModule,
          envType
        ]
      where
        envType = C.TypE (C.TyAll (C.TyEnvt [C.Type (C.TyArr (C.TyVar 0) (C.TyVar 0))]))

        envModule =
          C.ExpE
            ( C.Anno
                ( C.TLam
                    ( C.FEnv
                        [ C.ExpE
                            ( C.Anno
                                (C.Lam (C.Var 0))
                                (C.TyArr (C.TyVar 0) (C.TyVar 0))
                            )
                        ]
                    )
                )
                (C.TyVar 0) 
            )

        intResult =
          C.ExpE
            ( C.Anno
                ( C.Box
                    [C.ExpE (C.TApp (C.Var 0) (C.TyLit C.TyInt))]
                    (C.App (C.RProj (C.Var 0) "id") (C.Lit (C.LitInt 1)))
                )
                (C.TyLit C.TyInt)
            )

        boolResult =
          C.ExpE
            ( C.Anno
                ( C.Box
                    [C.ExpE (C.TApp (C.Var 1) (C.TyLit C.TyBool))]
                    (C.App (C.RProj (C.Var 0) "id") (C.Lit (C.LitBool True)))
                )
                (C.TyLit C.TyBool)
            )

main :: IO ()
main = hspec spec
