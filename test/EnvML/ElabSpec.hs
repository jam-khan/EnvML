module EnvML.ElabSpec where

import qualified Core.Syntax as C
import Data.Either (isLeft, isRight)
import EnvML.Elab
import qualified EnvML.Syntax as S
import Test.Hspec

tInt :: S.Typ
tInt = S.TyLit S.TyInt

tBool :: S.Typ
tBool = S.TyLit S.TyBool

intE :: Int -> S.Exp
intE i = S.Lit (S.LitInt i)

var :: Int -> S.Exp
var = S.Var

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "EnvML Elaboration" $ do
    -- describe "Inference (elabExpInfer)" inferSpec
    -- describe "Checking (elabExpCheck / annotations)" checkSpec
    -- placeholder
    it "placeholder test" $ do
      True `shouldBe` True

-- inferSpec :: Spec
-- inferSpec = do
--   describe "Literals" $ do
--     it "infers Int literals" $ do
--       elabExpInfer [] (intE 42)
--         `shouldBe` Right (tInt, C.Lit (C.LitInt 42))
--
--     it "infers Bool literals" $ do
--       elabExpInfer [] (S.Lit (S.LitBool True))
--         `shouldBe` Right (tBool, C.Lit (C.LitBool True))
--
--   describe "Variables" $ do
--     it "infers bound variables from the environment" $ do
--       elabExpInfer [S.Type tInt] (var 0)
--         `shouldBe` Right (tInt, C.Var 0)
--
--     it "fails on unbound variables" $ do
--       elabExpInfer [] (var 0)
--         `shouldSatisfy` isLeft
--
--   describe "Applications" $ do
--     it "infers application result type" $ do
--       let fnTy = S.TyArr tInt tInt
--       let fn = S.Anno (S.Lam (var 0)) fnTy
--       let expr = S.App fn (intE 42)
--
--       case elabExpInfer [] expr of
--         Right (t, C.App _ _) -> t `shouldBe` tInt
--         res -> expectationFailure $ show res
--
--     it "rejects argument type mismatch" $ do
--       let fnTy = S.TyArr tInt tInt
--       let fn = S.Anno (S.Lam (var 0)) fnTy
--       let expr = S.App fn (S.Lit (S.LitBool True))
--
--       elabExpInfer [] expr `shouldSatisfy` isLeft
--
--   describe "Polymorphism" $ do
--     it "infers type abstraction (TLam)" $ do
--       let inner =
--             S.Anno
--               (S.Lam (var 0))
--               (S.TyArr (S.TyVar 0) (S.TyVar 0))
--
--       case elabExpInfer [] (S.TLam inner) of
--         Right (S.TyAll _, C.TLam _) -> pure ()
--         res -> expectationFailure $ show res
--
--     it "infers type application (TApp)" $ do
--       let inner =
--             S.Anno
--               (S.Lam (var 0))
--               (S.TyArr (S.TyVar 0) (S.TyVar 0))
--
--       let polyId = S.TLam inner
--
--       case elabExpInfer [] (S.TApp polyId tInt) of
--         Right (_, C.TApp _ _) -> pure ()
--         res -> expectationFailure $ show res
--
--   describe "First-Class Environments (FEnv)" $ do
--     it "infers empty FEnv" $ do
--       elabExpInfer [] (S.FEnv [])
--         `shouldBe` Right (S.TyEnvt [], C.FEnv [])
--
--     it "infers singleton value FEnv" $ do
--       case elabExpInfer [] (S.FEnv [S.ExpE (intE 1)]) of
--         Right (S.TyEnvt [S.Type t], _) -> t `shouldBe` tInt
--         res -> expectationFailure $ show res
--
--     it "infers dependent value FEnv" $ do
--       let expr =
--             S.FEnv
--               [ S.ExpE (var 0), 
--                 S.ExpE (intE 1)
--               ]
--
--       case elabExpInfer [] expr of
--         Right (S.TyEnvt [S.Type ty, S.Type tx], _) -> do
--           tx `shouldBe` tInt
--           ty `shouldBe` tInt
--         res -> expectationFailure $ show res
--
--     it "infers mixed type/value FEnv" $ do
--       let expr =
--             S.FEnv
--               [ S.ExpE (S.Anno (intE 1) (S.TyVar 0)),
--                 S.TypE tInt
--               ]
--
--       case elabExpInfer [] expr of
--         Right (S.TyEnvt [S.Type _, S.TypeEq _], _) -> pure ()
--         res -> expectationFailure $ show res
--
-- checkSpec :: Spec
-- checkSpec = do
--   describe "Annotated lambdas" $ do
--     it "checks lambda against annotated type" $ do
--       let ty = S.TyArr tInt tInt
--       let expr = S.Anno (S.Lam (var 0)) ty
--
--       case elabExpInfer [] expr of
--         Right (t, C.Anno (C.Lam _) _) -> t `shouldBe` ty
--         res -> expectationFailure $ show res
