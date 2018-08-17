{-# LANGUAGE OverloadedLabels #-}

module RecEquiSpec (spec) where

import Test.Hspec
import TaPL.RecEqui

import Control.Lens ((#))
import Data.Extensible
import Data.Extensible.Effect.Default

spec :: Spec
spec = do
  describe "Type" $ do
    it "show primitive type" $ do
      let ty = Type (#primitive # SString "Int") :: NamedType
      show ty `shouldBe` "Int"
    it "show variable" $ do
      let ty = Type (#variable # VariableType (#id @= SString "X" <: nil)) :: NamedType
      show ty `shouldBe` "X"
    it "show arrow type" $ do
      let ty = Type (#variable # VariableType (#id @= SString "X" <: nil)) :: NamedType
          ty' = Type (#arrow # ArrowType (#domain @= ty <: #codomain @= ty <: nil)) :: NamedType
      show ty' `shouldBe` "X -> X"
    it "show recursion type" $ do
      let ty = Type (#variable # VariableType (#id @= SString "X" <: nil)) :: NamedType
          ty' = Type (#recursion # RecursionType (#name @= SString "X" <: #body @= ty <: nil)) :: NamedType
      show ty' `shouldBe` "(μX.X)"
  describe "Term" $ do
    it "show variable term" $ do
      let t = Term (#variable # VariableTerm (#id @= SString "x" <: nil)) :: NamedTerm
      show t `shouldBe` "x"
    it "show abstraction term" $ do
      let t = Term (#variable # VariableTerm (#id @= SString "x" <: nil)) :: NamedTerm
          ty = Type (#variable # VariableType (#id @= SString "X" <: nil)) :: NamedType
          t' = Term (#abstraction # AbstractionTerm (#name @= SString "x" <: #type @= ty <: #body @= t <: nil)) :: NamedTerm
      show t' `shouldBe` "(λx:X.x)"
  describe "UnName" $ do
    it "μX.X" $ do
      let ty = Type (#variable # VariableType (#id @= SString "X" <: nil)) :: NamedType
          ty' = Type (#recursion # RecursionType (#name @= SString "X" <: #body @= ty <: nil)) :: NamedType
          expected = Type (#recursion # RecursionType (#name @= SString "X" <: #body @= Type (#variable # VariableType (#id @= 0 <: nil)) <: nil)) :: UnNamedType
      run [] (unName ty') `shouldBe` Right expected
    it "λx:X.x" $ do
      let t = Term (#variable # VariableTerm (#id @= SString "x" <: nil)) :: NamedTerm
          ty = Type (#primitive # SString "X") :: NamedType
          t' = Term (#abstraction # AbstractionTerm (#name @= SString "x" <: #type @= ty <: #body @= t <: nil)) :: NamedTerm
          ty' = Type (#primitive # SString "X") :: UnNamedType
          t'' = Term (#variable # VariableTerm (#id @= 0 <: nil)) :: UnNamedTerm
          expected = Term $ #abstraction # AbstractionTerm (#name @= SString "x" <: #type @= ty' <: #body @= t'' <: nil) :: UnNamedTerm
      run [] (unName t') `shouldBe` Right expected