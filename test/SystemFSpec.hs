{-# LANGUAGE OverloadedLabels #-}

module SystemFSpec (spec) where
  
import Test.Hspec
import TaPL.SystemF

import RIO
import System.IO

import Data.Extensible
import Data.Extensible.Effect.Default


spec :: Spec
spec = do
  describe "unName/restoreName" $ do
    it "λX.λx:X.x -> λX.λx:1.0" $ do
      let t = TypeAbstractionTerm (#name @= "X" <: #body @= AbstractionTerm (#name @= "x" <: #type @= VariableType "X" <: #body @= VariableTerm "x" <: nil) <: nil)
          expected = TypeAbstractionTerm (#name @= "X" <: #body @= AbstractionTerm (#name @= "x" <: #type @= VariableType 0 <: #body @= VariableTerm 0 <: nil) <: nil)
      leaveUnName [] t `shouldBe` Right expected
    it "λX.λx:1.0 -> λX.λx:X.x" $ do
      let t = TypeAbstractionTerm (#name @= "X" <: #body @= AbstractionTerm (#name @= "x" <: #type @= VariableType 0 <: #body @= VariableTerm 0 <: nil) <: nil)
          expected = TypeAbstractionTerm (#name @= "X" <: #body @= AbstractionTerm (#name @= "x" <: #type @= VariableType "X" <: #body @= VariableTerm "x" <: nil) <: nil)
      leaveRestoreName [] t `shouldBe` Right expected
    it "∀X.∀Y.X->Y" $ do
      let ty = AllType (#name @= "X" <: #body @= AllType (#name @= "Y" <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil) <: nil) <: nil)
          expected = AllType (#name @= "X" <: #body @= AllType (#name @= "Y" <: #body @= ArrowType (#domain @= VariableType 1 <: #codomain @= VariableType 0 <: nil) <: nil) <: nil)
      leaveUnName [] ty `shouldBe` Right expected
  describe "beta reduction" $ do
    it "(λx:Nat->Nat.λy:Nat.x y) (λx:Nat.x) --> λy:Nat (λx:Nat.x) y" $ do
      let s = AbstractionTerm (#name @= "x" <: #type @= PrimitiveType "Nat" <: #body @= VariableTerm "x" <: nil)
          t = AbstractionTerm (#name @= "y" <: #type @= PrimitiveType "Nat" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil)
          expected = AbstractionTerm (#name @= "y" <: #type @= PrimitiveType "Nat" <: #body @= ApplicationTerm (#function @= AbstractionTerm (#name @= "x" <: #type @= PrimitiveType "Nat" <: #body @= VariableTerm "x" <: nil) <: #argument @= VariableTerm "y" <: nil) <: nil)
      leaveBetaReduction [("x", VariableTermBind)] s t `shouldBe` Right expected
    it "(λX.λx:X.x) [Nat] --> λx:Nat.x" $ do
      let s = PrimitiveType "Nat"
          t = AbstractionTerm (#name @= "x" <: #type @= VariableType "X" <: #body @= VariableTerm "x" <: nil)
          expected = AbstractionTerm (#name @= "x" <: #type @= PrimitiveType "Nat" <: #body @= VariableTerm "x" <: nil)
      leaveBetaReduction [("X", VariableTypeBind)] s t `shouldBe` Right expected
  describe "eval" $ do
    it "let {X, x} = {*Nat, λx:Nat.x} as {∃X, X->X} in (λf:X->X.λx:X.f x) x --> (λf:Nat->Nat.λx:Nat. f x) (λx:Nat.x)" $ do
      let p = PackageTerm (#type @= PrimitiveType "Nat" <: #term @= AbstractionTerm (#name @= "x" <: #type @= PrimitiveType "Nat" <: #body @= VariableTerm "x" <: nil) <: #exist @= ExistType (#name @= "X" <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil) <: nil) <: nil)
          t = UnPackageTerm (#type @= "X" <: #name @= "x" <: #body @= p <: #in @= ApplicationTerm (#function @= AbstractionTerm (#name @= "f" <: #type @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil) <: #body @= AbstractionTerm (#name @= "x" <: #type @= VariableType "X" <: #body @= ApplicationTerm (#function @= VariableTerm "f" <: #argument @= VariableTerm "x" <: nil) <: nil) <: nil) <: #argument @= VariableTerm "x" <: nil) <: nil)
          expected = AbstractionTerm (#name @= "x" <: #type @= PrimitiveType "Nat" <: #body @= ApplicationTerm (#function @= AbstractionTerm (#name @= "x" <: #type @= PrimitiveType "Nat" <: #body @= VariableTerm "x" <: nil) <: #argument @= VariableTerm "x" <: nil) <: nil)
      leaveEval [] t `shouldBe` Right expected
    it "id [Nat] 0" $ do
      let t = ApplicationTerm (#function @= TypeApplicationTerm (#term @= TypeAbstractionTerm (#name @= "X" <: #body @= AbstractionTerm (#name @= "x" <: #type @= VariableType "X" <: #body @= VariableTerm "x" <: nil) <: nil) <: #type @= PrimitiveType "Nat" <: nil) <: #argument @= ConstTerm "0" <: nil) 
          expected = ConstTerm "0"
      leaveEval [] t `shouldBe` Right expected
  describe "typing" $ do
    it "id=λx.x: ∀X.X->X" $ do
      let t = TypeAbstractionTerm (#name @= "X" <: #body @= AbstractionTerm (#name @= "x" <: #type @= VariableType "X" <: #body @= VariableTerm "x" <: nil) <: nil)
          expected = AllType (#name @= "X" <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil) <: nil)
      leaveTyping [] t `shouldBe` Right expected
    it "id [Nat]: Nat->Nat" $ do
      let t = TypeApplicationTerm (#term @= TypeAbstractionTerm (#name @= "X" <: #body @= AbstractionTerm (#name @= "x" <: #type @= VariableType "X" <: #body @= VariableTerm "x" <: nil) <: nil) <: #type @= PrimitiveType "Nat" <: nil)
          expected = ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= PrimitiveType "Nat" <: nil)
      leaveTyping [] t `shouldBe` Right expected
    it "selfApp: (∀X.X->X)->(∀X.X->X)" $ do
      let t = AbstractionTerm (#name @= "x" <: #type @= AllType (#name @= "X" <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil) <: nil) <: #body @= ApplicationTerm (#function @= TypeApplicationTerm (#term @= VariableTerm "x" <: #type @= AllType (#name @= "X" <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil) <: nil) <: nil) <: #argument @= VariableTerm "x" <: nil) <: nil)
          expected = ArrowType (#domain @= AllType (#name @= "X" <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil) <: nil) <: #codomain @= AllType (#name @= "X" <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil) <: nil) <: nil)
      leaveTyping [] t `shouldBe` Right expected
    it "counterADT" $ do
      let counterADT = PackageTerm (#type @= NatType <: #term @= RecordTerm [("new", Succ Zero), ("get", AbstractionTerm (#name @= "i" <: #type @= NatType <: #body @= VariableTerm "i" <: nil)), ("inc", AbstractionTerm (#name @= "i" <: #type @= NatType <: #body @= Succ (VariableTerm "i") <: nil))] <: #exist @= ExistType (#name @= "Counter" <: #body @= RecordType [("new", VariableType "Counter"), ("get", ArrowType (#domain @= VariableType "Counter" <: #codomain @= NatType <: nil)), ("inc", ArrowType (#domain @= VariableType "Counter" <: #codomain @= VariableType "Counter" <: nil))] <: nil) <: nil)
          t = UnPackageTerm (#type @= "Counter" <: #name @= "counter" <: #body @= counterADT <: #in @= ApplicationTerm (#function @= ProjectionTerm (#term @= VariableTerm "counter" <: #label @= "get" <: nil) <: #argument @= ApplicationTerm (#function @= ProjectionTerm (#term @= VariableTerm "counter" <: #label @= "inc" <: nil) <: #argument @= ProjectionTerm (#term @= VariableTerm "counter" <: #label @= "new" <: nil) <: nil) <: nil) <: nil)
          expected = NatType 
      leaveTyping [] t `shouldBe` Right expected
