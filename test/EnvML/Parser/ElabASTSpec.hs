module EnvML.Parser.ElabASTSpec (spec) where

import qualified EnvML.Parser.AST as N
import EnvML.Parser.ElabAST
import qualified EnvML.Syntax as D
import Test.Hspec

spec :: Spec
spec = do
  describe "elabTyp" $ do
    it "elaborates literal types" $ do
      elabTyp [] (N.TyLit N.TyInt)
        `shouldBe` D.TyLit D.TyInt
      elabTyp [] (N.TyLit N.TyBool)
        `shouldBe` D.TyLit D.TyBool

    it "elaborates type variables using De Bruijn indices" $ do
      elabTyp ["A", "B", "C"] (N.TyVar "A")
        `shouldBe` D.TyVar 0
      elabTyp ["A", "B", "C"] (N.TyVar "B")
        `shouldBe` D.TyVar 1
      elabTyp ["A", "B", "C"] (N.TyVar "C")
        `shouldBe` D.TyVar 2

    it "elaborates arrow types" $ do
      elabTyp [] (N.TyArr (N.TyLit N.TyInt) (N.TyLit N.TyBool))
        `shouldBe` D.TyArr (D.TyLit D.TyInt) (D.TyLit D.TyBool)

    it "elaborates universal types (TyAll)" $ do
      elabTyp [] (N.TyAll "A" (N.TyVar "A"))
        `shouldBe` D.TyAll (D.TyVar 0)

    it "handles nested TyAll binders correctly" $ do
      elabTyp [] (N.TyAll "A" (N.TyAll "B" (N.TyVar "A")))
        `shouldBe` D.TyAll (D.TyAll (D.TyVar 1))

    it "elaborates TyBoxT correctly" $ do
      let ty = N.TyBoxT [("A", N.TypeEq (N.TyLit N.TyInt)), ("B", N.TypeEq (N.TyLit N.TyBool))] (N.TyVar "A")
      elabTyp ["X"] ty
        `shouldBe` D.TyBoxT 
                       [D.TypeEq (D.TyLit D.TyInt), D.TypeEq (D.TyLit D.TyBool)]
                       (D.TyVar 1)

    it "elaborates record types" $ do
      let ty = N.TyRcd "x" (N.TyLit N.TyInt)
      elabTyp [] ty `shouldBe` D.TyRcd "x" (D.TyLit D.TyInt)

    it "elaborates environment types with multiple bindings + reversal" $ do
      let ty = N.TyEnvt [("A", N.Type (N.TyLit N.TyInt)), ("B", N.Kind), ("C", N.TypeEq (N.TyVar "A"))]
      elabTyp [] ty `shouldBe` D.TyEnvt [D.TypeEq (D.TyVar 1), D.Kind, D.Type (D.TyLit D.TyInt)]

    it "elaborates module types" $ do
      let mt = N.TyArrowM (N.TyLit N.TyInt) (N.TySig [N.ValDecl "x" (N.TyLit N.TyInt)])
      elabModuleTyp [] mt
        `shouldBe` D.TyArrowM (D.TyLit D.TyInt) (D.TySig [D.ValDecl (D.TyLit D.TyInt)])

  describe "elabExp" $ do
    it "elaborates literal expressions" $ do
      elabExp [] (N.Lit (N.LitInt 3))
        `shouldBe` D.Lit (D.LitInt 3)
      elabExp [] (N.Lit (N.LitBool True))
        `shouldBe` D.Lit (D.LitBool True)

    it "elaborates variables using De Bruijn indices" $ do
      elabExp ["x", "y"] (N.Var "x")
        `shouldBe` D.Var 0
      elabExp ["x", "y"] (N.Var "y")
        `shouldBe` D.Var 1

    it "elaborates lambdas correctly" $ do
      elabExp [] (N.Lam "x" (N.Var "x"))
        `shouldBe` D.Lam (D.Var 0)

    it "shifts outer variables under lambdas" $ do
      elabExp ["y"] (N.Lam "x" (N.Var "y"))
        `shouldBe` D.Lam (D.Var 1)

    it "elaborates applications" $ do
      elabExp ["f", "x"] (N.App (N.Var "f") (N.Var "x"))
        `shouldBe` D.App (D.Var 0) (D.Var 1)

    it "elaborates type lambdas" $ do
      elabExp [] (N.TLam "A" (N.Lam "x" (N.Var "x")))
        `shouldBe` D.TLam (D.Lam (D.Var 0))

    it "elaborates type applications" $ do
      elabExp ["f"] (N.TApp (N.Var "f") (N.TyLit N.TyInt))
        `shouldBe` D.TApp (D.Var 0) (D.TyLit D.TyInt)

    it "elaborates closures with environments + env reversal" $ do
      let env = [("x", N.ExpE (N.Lit (N.LitInt 1))), ("y", N.ExpE (N.Var "x"))]
      elabExp [] (N.Clos env "y" (N.Var "y"))
        `shouldBe` D.Clos [D.ExpE (D.Var 0), D.ExpE (D.Lit (D.LitInt 1))] (D.Var 0)

    it "elaborates type closures with environments + env reversal" $ do
      let env = [("x", N.ExpE (N.Lit (N.LitInt 1))), ("y", N.ExpE (N.Var "x"))]
      elabExp [] (N.TClos env "y" (N.Var "y"))
        `shouldBe` D.TClos [D.ExpE (D.Var 0), D.ExpE (D.Lit (D.LitInt 1))] (D.Var 0)

    it "elaborates boxes correctly" $ do
      let env = [("a", N.ExpE (N.Lit (N.LitInt 10)))]
          ex = N.Box env (N.Var "a")
      elabExp [] ex `shouldBe` D.Box [D.ExpE (D.Lit (D.LitInt 10))] (D.Var 0)

    it "elaborates boxes with multiple bindings + reversal" $ do
      let env = [("a", N.ExpE (N.Lit (N.LitInt 10))), ("b", N.ExpE (N.Var "a"))]
          ex = N.Box env (N.Var "a")
      elabExp [] ex `shouldBe` D.Box [D.ExpE (D.Var 0), D.ExpE (D.Lit (D.LitInt (10)))] (D.Var 0)

    it "elaborates record projections" $ do
      let ex = N.RProj (N.Rec "x" (N.Lit (N.LitInt 5))) "x"
      elabExp [] ex `shouldBe` D.RProj (D.Rec "x" (D.Lit (D.LitInt 5))) "x"

    it "elaborates FEnv with multiple bindings + reversal" $ do
      let env = [("x", N.ExpE (N.Lit (N.LitInt 1))), ("y", N.ExpE (N.Var "x"))]
      elabExp [] (N.FEnv env)
        `shouldBe` D.FEnv [D.ExpE (D.Var 0), D.ExpE (D.Lit (D.LitInt 1))]

    it "elaborates annotated expressions" $ do
      let ex = N.Anno (N.Var "x") (N.TyLit N.TyInt)
      elabExp ["x"] ex `shouldBe` D.Anno (D.Var 0) (D.TyLit D.TyInt)

  describe "elabIntf" $ do
    it "elaborates interfaces in reverse order" $ do
      let intf =
            [ N.TyDef "A" (N.TyLit N.TyInt)
            , N.ValDecl "x" (N.TyVar "A")
            , N.TyDef "B" (N.TyLit N.TyBool)
            , N.ValDecl "y" (N.TyVar "B")
            , N.ValDecl "z" (N.TyVar "A")
            ]
      elabIntf [] intf
        `shouldBe` [ D.ValDecl (D.TyVar 3)
                   , D.ValDecl (D.TyVar 0)
                   , D.TyDef (D.TyLit D.TyBool)
                   , D.ValDecl (D.TyVar 0)
                   , D.TyDef (D.TyLit D.TyInt)
                   ]

  describe "elabModule" $ do
    it "elaborates structs with environments + reversal" $ do
      let env = [("x", N.ExpE (N.Lit (N.LitInt 1))), ("y", N.ExpE (N.Var "x"))]
      elabModule [] (N.Struct [] env)
        `shouldBe` D.Struct [D.ExpE (D.Var 0), D.ExpE (D.Lit (D.LitInt 1))]

    it "elaborates structs with imports as functors" $ do
      let imps = [("A", N.TyLit N.TyInt), ("B", N.TyLit N.TyBool)]
          env = [("x", N.ExpE (N.Lit (N.LitInt 1)))]
      elabModule [] (N.Struct imps env)
        `shouldBe` D.Functor (D.TyLit D.TyInt) (D.Functor (D.TyLit D.TyBool) (D.Struct [D.ExpE (D.Lit (D.LitInt 1))]))

    it "elaborates functors" $ do
      let m = N.Functor "X" (N.TyLit N.TyInt) (N.Struct [] [("x", N.ExpE (N.Var "X"))])
      elabModule [] m `shouldBe` D.Functor (D.TyLit D.TyInt) (D.Struct [D.ExpE (D.Var 0)])

    it "elaborates module applications regardless of no functors (no checks in this phase)" $ do
      let m1 = N.Struct [] [("x", N.ExpE (N.Lit (N.LitInt 1)))]
          m2 = N.Struct [] []
      elabModule [] (N.MApp m1 m2) `shouldBe` D.MApp (D.Struct [D.ExpE (D.Lit (D.LitInt 1))]) (D.Struct [])

    it "elaborates module links" $ do
      let m1 = N.Struct [] []
          m2 = N.Struct [] []
      elabModule [] (N.MLink m1 m2) `shouldBe` D.MLink (D.Struct []) (D.Struct [])
