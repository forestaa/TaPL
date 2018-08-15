module SimplyTypedSpec (spec) where

import Test.Hspec
import TaPL.SimplyTyped

spec :: Spec
spec = do
  describe "eval" $ do
    it "exercise 9.2.2 (1)" $ do
      let ctx1 = [("f", VarBind $ TyArrow TyBool TyBool)]
          t1   = TmApp (TmVar "f") (TmIf TmFalse TmTrue TmFalse)
      eval ctx1 t1 `shouldBe` Right ((TmApp (TmVar "f") (TmIf TmFalse TmTrue TmFalse)), TyBool)
