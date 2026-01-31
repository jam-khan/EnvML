{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}

module Examples.ForAll.Example0Spec where

import qualified Core.Syntax as C
import qualified EnvML.Elab as ElabD
import qualified EnvML.Syntax as D
import qualified EnvML.Parser.ElabAST as ElabN
import qualified EnvML.Parser.AST as N
import Data.Either (isLeft, isRight)
import EnvML.Parser.Parse (parseEmlFile)
import Test.Hspec

examplePath :: String
examplePath = "examples/ForAll/Example0.eml"

spec :: Spec
spec = do
  parsedData <- runIO $ parseEmlFile examplePath
  describe "Example 0: Basic Modules with Manifest Types" $ do
    it "parses successfully" $ do
      parsedData `shouldBe` expectedAst

    it "pre-processes (de-bruijn transform + de-sugar) successfully" $ do
      let astElabExpr = ElabN.elabModule [] parsedData
      astElabExpr `shouldBe` expectedEnvMLExpr

    it "elaborates successfully" $ do
      let envMLElabExpr = ElabD.elabM expectedEnvMLExpr
      envMLElabExpr `shouldBe` (Right expectedCoreExpr)
  where
    -- it "type checks at core successfully" $ do
    -- it "types for elaboration and core match" $ do
    -- it "evaluates successfully" $ do

    expectedAst =
      N.Struct
        []
        [ ("ENV", envType),
          ("env", envModule),
          ("result", resultExpr)
        ]
      where
        envType =
          N.ModTypE $
            N.TyModule $
              N.TySig
                [ N.TyDef "t" (N.TyLit N.TyInt),
                  N.ValDecl "inc" (N.TyArr (N.TyVar "t") (N.TyVar "t"))
                ]

        envModule =
          N.ModExpE $
            N.Anno
              ( N.ModE $
                  N.Struct
                    []
                    [ ("t", N.TypE (N.TyLit N.TyInt)),
                      ( "inc",
                        N.ExpE
                          ( N.Anno
                              (N.Lam [("n", N.TmArg)] (N.BinOp $ N.Add (N.Var "n") (N.Lit (N.LitInt 1))))
                              (N.TyArr (N.TyVar "t") (N.TyVar "t"))
                          )
                      )
                    ]
              )
              (N.TyVar "ENV")

        resultExpr =
          N.ExpE $
            N.Anno
              ( N.Box
                  [("x", N.ExpE (N.Var "env"))]
                  (N.App (N.RProj (N.Var "x") "inc") (N.Lit (N.LitInt 10)))
              )
              (N.TyLit N.TyInt)

    expectedEnvMLExpr =
      D.Struct
        [ (resultExpr),
          (envModule),
          (envType)
        ]
      where
        envType =
          D.ModTypE $
            D.TyModule $
              D.TySig
                [ D.ValDecl (D.TyArr (D.TyVar 0) (D.TyVar 0)),
                  D.TyDef (D.TyLit D.TyInt)
                ]
        envModule =
          D.ModExpE $
            D.Anno
              ( D.ModE $
                  D.Struct
                    [ ( D.ExpE
                          ( D.Anno
                              (D.Lam (D.BinOp $ D.Add (D.Var 0) (D.Lit (D.LitInt 1))))
                              (D.TyArr (D.TyVar 0) (D.TyVar 0))
                          )
                      ),
                      (D.TypE (D.TyLit D.TyInt))
                    ]
              )
              (D.TyVar 0)
        resultExpr =
          D.ExpE $
            D.Anno
              ( D.Box
                  [(D.ExpE (D.Var 0))]
                  (D.App (D.RProj (D.Var 0) "inc") (D.Lit (D.LitInt 10)))
              )
              (D.TyLit D.TyInt)
    expectedCoreExpr =
      C.FEnv [resultExpr, envModule, envType]
      where
        envType =
          C.TypE $
            C.TyEnvt
              [ C.Type (C.TyArr (C.TyVar 0) (C.TyVar 0)),
                C.Type (C.TyLit C.TyInt)
              ]

        envModule =
          C.ExpE $
            C.Anno
              ( C.FEnv
                  [ C.ExpE
                      ( C.Anno
                          (C.Lam (C.BinOp (C.Add (C.Var 0) (C.Lit (C.LitInt 1)))))
                          (C.TyArr (C.TyVar 0) (C.TyVar 0))
                      ),
                    C.TypE (C.TyLit C.TyInt)
                  ]
              )
              (C.TyVar 0)

        resultExpr =
          C.ExpE $
            C.Anno
              ( C.Box
                  [C.ExpE (C.Var 0)]
                  (C.App (C.RProj (C.Var 0) "inc") (C.Lit (C.LitInt 10)))
              )
              (C.TyLit C.TyInt)
