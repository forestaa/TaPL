module SubTypedSpec (spec) where

import Test.Hspec
import TaPL.SubTyped

import RIO
import qualified RIO.Map as Map

spec :: Spec
spec = do
  describe "isSubType" $ do
    it "exercise 15.2.1" $ do
      let ty1 = TyRecord $ Map.fromList [("x", TyTop), ("y", TyTop), ("z", TyTop)]
          ty2 = TyRecord $ Map.fromList [("y", TyTop)]
      isSubType ty1 ty2 `shouldBe` True
    it "exercise 15.2.3" $ do
      let ty1 = TyRecord $ Map.fromList [("a", TyTop), ("b", TyTop)]
          ty2 = TyRecord $ Map.fromList [("a", TyTop), ("b", TyTop)]
      isSubType ty1 ty2 `shouldBe` True
    it "exercise 15.2.3" $ do
      let ty1 = TyRecord $ Map.fromList [("a", TyTop), ("b", TyTop)]
          ty2 = TyRecord $ Map.fromList [("b", TyTop), ("a", TyTop)]
      isSubType ty1 ty2 `shouldBe` True
    it "exercise 15.2.3" $ do
      let ty1 = TyRecord $ Map.fromList [("a", TyTop), ("b", TyTop)]
          ty2 = TyRecord $ Map.fromList [("a", TyTop)]
      isSubType ty1 ty2 `shouldBe` True
    it "exercise 15.2.3" $ do
      let ty1 = TyRecord $ Map.fromList [("a", TyTop), ("b", TyTop)]
          ty2 = TyRecord $ Map.fromList [("b", TyTop)]
      isSubType ty1 ty2 `shouldBe` True
    it "exercise 15.2.3" $ do
      let ty1 = TyRecord $ Map.fromList [("a", TyTop), ("b", TyTop)]
          ty2 = TyRecord $ Map.fromList []
      isSubType ty1 ty2 `shouldBe` True
    it "exercise 15.2.3" $ do
      let ty1 = TyRecord $ Map.fromList [("a", TyTop), ("b", TyTop)]
          ty2 = TyTop
      isSubType ty1 ty2 `shouldBe` True
    it "arrow type" $ do
      let ty1 = TyArrow (TyRecord $ Map.fromList []) (TyRecord $ Map.fromList [("x", TyTop), ("y", TyTop)])
          ty2 = TyArrow (TyRecord $ Map.fromList [("x", TyTop)]) (TyRecord $ Map.fromList [("x", TyTop)])
      isSubType ty1 ty2 `shouldBe` True
  describe "eval" $ do
      it "record" $ do
        let ctx = [("top", VarBind TyTop)] 
            t = TmProj (TmRecord $ Map.fromList [("x", TmVar "top")]) "x"
        eval ctx t `shouldBe` Right  (TmVar "top", TyTop)
      it "arrow" $ do
        let ctx = [("top", VarBind TyTop), ("f", VarBind $ TyArrow TyTop TyTop)]
            t = TmApp (TmAbs "x" (TyRecord $ Map.fromList [("x", TyTop)]) (TmProj (TmVar "x") "x")) (TmRecord $ Map.fromList [("x", TmVar "top"), ("y", TmVar "f")])
        eval ctx t `shouldBe` Right (TmVar "top", TyTop)