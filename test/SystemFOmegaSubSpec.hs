{-# LANGUAGE OverloadedLabels #-}

module SystemFOmegaSubSpec (spec) where

import Test.Hspec
import TaPL.SystemFOmegaSub

import TaPL.NameLess
import SString

import RIO

import Data.Extensible


spec :: Spec
spec = do
  describe "unName/restoreName" $ do
    it "λX.X ---> λX.0" $ do
      let ty = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType "X" <: nil)
          expected = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType 0 <: nil)
      leaveUnName [] ty `shouldBe` Right expected
    it "λX.0 ---> λX.X" $ do
      let ty = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType 0 <: nil)
          expected = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType "X" <: nil)
      leaveRestoreName [] ty `shouldBe` Right expected
    it "λX.∀Y<:X.Y" $ do
      let ty = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= UniversalType (#name @= "Y" <: #bound @= VariableType "X" <: #body @= VariableType "Y" <: nil) <: nil)
          expected = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= UniversalType (#name @= "Y" <: #bound @= VariableType 0 <: #body @= VariableType 0 <: nil) <: nil)
      leaveUnName [] ty `shouldBe` Right expected
    it "λX.(λY.X->Y Top) Top" $ do
      let ty = ApplicationType (#function @= AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ApplicationType (#function @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil) <: nil) <: #argument @= TopType <: nil) <: nil) <: #argument @= TopType <: nil)
          expected = ApplicationType (#function @= AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ApplicationType (#function @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= VariableType 1 <: #codomain @= VariableType 0 <: nil) <: nil) <: #argument @= TopType <: nil) <: nil) <: #argument @= TopType <: nil)
      leaveUnName [] ty `shouldBe` Right expected
  describe "simplify" $ do
    it "λX.(λY.X->Y Top) Top ---> Top -> Top" $ do
      let ty = ApplicationType (#function @= AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ApplicationType (#function @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil) <: nil) <: #argument @= TopType <: nil) <: nil) <: #argument @= TopType <: nil)
          expected = ArrowType (#domain @= TopType <: #codomain @= TopType <: nil)
      leaveNormalize [] ty `shouldBe` Right expected
    it "λX.(λY.X->Y Top) --> λX.(λY.X->Y Top)" $ do
      let ty = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ApplicationType (#function @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil) <: nil) <: #argument @= TopType <: nil) <: nil)
          expected = ty
      leaveNormalize [] ty `shouldBe` Right expected
  describe "subtype" $ do
    let idType = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType "X" <: nil)
        idType' = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType 0 <: nil)
        ctx = [("F", TypedVariableTypeBind idType'), ("A", TypedVariableTypeBind (VariableType 0)), ("B", TypedVariableTypeBind TopType)]
    it "ctx |- A <: Id B" $ do
      let left = VariableType "A"
          right = ApplicationType (#function @= idType <: #argument @= VariableType "B" <: nil)
      leaveIsSubTypeOf ctx left right `shouldBe` Right True
    it "ctx |- Id A <: B" $ do
      let left = ApplicationType (#function @= idType <: #argument @= VariableType "A" <: nil)
          right = VariableType "B"
      leaveIsSubTypeOf ctx left right `shouldBe` Right True
    it "ctx |- λX.X <: λX.Top" $ do
      let left = idType
          right = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= TopType <: nil)
      leaveIsSubTypeOf ctx left right `shouldBe` Right True
    it "ctx |- λX.∀Y<:X.Y <: λX.∀Y<:Top.Y" $ do
      let left = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= UniversalType (#name @= "Y" <: #bound @= VariableType "X" <: #body @= VariableType "Y" <: nil) <: nil)
          right = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= UniversalType (#name @= "Y" <: #bound @= TopType <: #body @= VariableType "Y" <: nil) <: nil)
      leaveIsSubTypeOf ctx left right `shouldBe` Right False
    it "ctx |- λX.∀Y<:X.Y <: λX.∀Y<:X.X" $ do
      let left = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= UniversalType (#name @= "Y" <: #bound @= VariableType "X" <: #body @= VariableType "Y" <: nil) <: nil)
          right = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= UniversalType (#name @= "Y" <: #bound @= VariableType "X" <: #body @= VariableType "X" <: nil) <: nil)
      leaveIsSubTypeOf ctx left right `shouldBe` Right True
    it "ctx |- F B <: B" $ do
      let left = ApplicationType (#function @= VariableType "F" <: #argument @= VariableType "B" <: nil) 
          right = VariableType "B" 
      leaveIsSubTypeOf ctx left right `shouldBe` Right True
    it "ctx |- B <: F B" $ do
      let left = VariableType "B" 
          right = ApplicationType (#function @= VariableType "F" <: #argument @= VariableType "B" <: nil) 
      leaveIsSubTypeOf ctx left right `shouldBe` Right False
    it "ctx |- F A <: F B" $ do
      let left = ApplicationType (#function @= VariableType "F" <: #argument @= VariableType "A" <: nil) 
          right = ApplicationType (#function @= VariableType "F" <: #argument @= VariableType "B" <: nil) 
      leaveIsSubTypeOf ctx left right `shouldBe` Right False
    it "ctx |- ∀G<:(λY.Top->Y).G A <: ∀G<:(λY.Top->Y).Top->B" $ do
      let left = UniversalType (#name @= "G" <: #bound @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= TopType <: #codomain @= VariableType "Y" <: nil) <: nil) <: #body @= ApplicationType (#function @= VariableType "G" <: #argument @= VariableType "A" <: nil) <: nil)
          right = UniversalType (#name @= "G" <: #bound @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= TopType <: #codomain @= VariableType "Y" <: nil) <: nil) <: #body @= ArrowType (#domain @= TopType <: #codomain @= VariableType "B" <: nil) <: nil)
      leaveIsSubTypeOf ctx left right `shouldBe` Right True
    it "ctx |- ∀G<:(λY.Top->Y).G A <: ∀G<:(λY.Top->Y).G B" $ do
      let left = UniversalType (#name @= "G" <: #bound @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= TopType <: #codomain @= VariableType "Y" <: nil) <: nil) <: #body @= ApplicationType (#function @= VariableType "G" <: #argument @= VariableType "A" <: nil) <: nil)
          right = UniversalType (#name @= "G" <: #bound @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= TopType <: #codomain @= VariableType "Y" <: nil) <: nil) <: #body @= ApplicationType (#function @= VariableType "G" <: #argument @= VariableType "B" <: nil) <: nil)
      leaveIsSubTypeOf ctx left right `shouldBe` Right False
    it "ctx |- Top[*->*] <: Top[*->*->*]" $ do
      let left = topOf $ ArrowKind (#domain @= StarKind <: #codomain @= StarKind <: nil)
          right = topOf $ ArrowKind (#domain @= StarKind <: #codomain @= ArrowKind (#domain @= StarKind <: #codomain @= StarKind <: nil) <: nil)
      leaveIsSubTypeOf ctx left right `shouldBe` Right False
    
