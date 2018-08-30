{-# LANGUAGE OverloadedLabels #-}

module ReconstructionSpec where

import Test.Hspec
import TaPL.Reconstruction

import RIO
import qualified RIO.Map as Map
import qualified RIO.Set as Set


import Data.Extensible
import Data.Extensible.Effect.Default

spec :: Spec
spec = do
  describe "unName/restoreName" $ do
    it "(λx:Nat. x, λx. x)" $ do
      let t = PairTerm (AbstractionTerm (#name @= "x" <: #type @= NatType <: #body @= VariableTerm "x" <: nil)) (ImplicitAbstractionTerm (#name @= "x" <: #body @= VariableTerm "x" <: nil))
      case leaveUnName [] t of
        Left e -> expectationFailure $ show e
        Right t' -> leaveRestoreName [] t' `shouldBe` Right t
    it "let ..." $ do
      let t = LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "x" <: #body @= PairTerm (VariableTerm "x") (VariableTerm "x") <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ImplicitAbstractionTerm (#name @= "x" <: #body @= VariableTerm "x" <: nil) <: nil) <: nil) <: nil) <: nil) <: nil) <: nil) <: nil)
      case leaveUnName [] t of
        Left e -> expectationFailure $ show e
        Right t' -> leaveRestoreName [] t' `shouldBe` Right t
  describe "reconstruction" $
    it "exercise 22.3.3" $ do
      let ctx = [("X", ConstTypeBind), ("Y", ConstTypeBind), ("Z", ConstTypeBind)]
          t = AbstractionTerm $ #name @= "x" <: #type @= VariableType "X" <: #body @= AbstractionTerm (#name @= "y" <: #type @= VariableType "Y" <: #body @= AbstractionTerm (#name @= "z" <: #type @= VariableType "Z" <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "z" <: nil) <: #argument @= ApplicationTerm (#function @= VariableTerm "y" <: #argument @= VariableTerm "z" <: nil) <: nil) <: nil) <: nil) <: nil
          expectedty = ArrowType $ #domain @= VariableType "X" <: #codomain @= ArrowType (#domain @= VariableType "Y" <: #codomain @= ArrowType (#domain @= VariableType "Z" <: #codomain @= VariableType "?X_2" <: nil) <: nil) <: nil
          expectedconstraints = [(VariableType "?X_0", ArrowType (#domain @= VariableType "?X_1" <: #codomain @= VariableType "?X_2" <: nil)), (VariableType "X", ArrowType (#domain @= VariableType "Z" <: #codomain @= VariableType "?X_0" <: nil)), (VariableType "Y", ArrowType (#domain @= VariableType "Z" <: #codomain @= VariableType "?X_1" <: nil))]
      case leaveUnName ctx t of
        Right t' -> leaveReconstruction ctx t' `shouldBe` Right (expectedty, expectedconstraints)
        Left _ -> expectationFailure "panic"
  describe "unify" $ do
    it "exercise 22.4.3 1" $ do
      let c = [(VariableType "X", NatType), (VariableType "Y", ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil))]
          expected = [("X", NatType), ("Y", ArrowType (#domain @= NatType <: #codomain @= NatType <: nil))]
      leaveEff (runEitherDef $ unify' c) `shouldBe` Right expected
    it "exercise 22.4.3 2" $ do
      let c = [(ArrowType (#domain @= NatType <: #codomain @= NatType <: nil), ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil))]
          expected = [("X", NatType), ("Y", NatType)]
      leaveEff (runEitherDef $ unify' c) `shouldBe` Right expected
    it "exercise 22.4.3 3" $ do
      let c = [(ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil), ArrowType (#domain @= VariableType "Y" <: #codomain @= VariableType "Z" <: nil)), (VariableType "Z", ArrowType (#domain @= VariableType "U" <: #codomain @= VariableType "W" <: nil))]
          expected = [("X", ArrowType (#domain @= VariableType "U" <: #codomain @= VariableType "W" <: nil)), ("Y", ArrowType (#domain @= VariableType "U" <: #codomain @= VariableType "W" <: nil)), ("Z", ArrowType (#domain @= VariableType "U" <: #codomain @= VariableType "W" <: nil))]
      leaveEff (runEitherDef $ unify' c) `shouldBe` Right expected
    it "exercise 22.4.3 4" $ do
      let c = [(NatType, ArrowType (#domain @= NatType <: #codomain @= VariableType "X" <: nil))]
      leaveEff (runEitherDef $ unify' c) `shouldBe` Left UnifyFailed
    it "exercise 22.4.3 5" $ do
      let c = [(VariableType "X", ArrowType (#domain @= NatType <: #codomain @= VariableType "X" <: nil))]
      leaveEff (runEitherDef $ unify'  c) `shouldBe` Left UnifyFailed
    it "exercise 22.4.3 6" $ do
      let c = []
      leaveEff (runEitherDef $ unify' c) `shouldBe` Right Map.empty
  describe "typeOf" $ do
    it "λx:X. x" $ do
      let t = AbstractionTerm (#name @= "x" <: #type @= VariableType "X" <: #body @= VariableTerm "x"<: nil)
          expected = ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "X" <: nil)
      case leaveUnName [] t of
        Left e -> expectationFailure $ show e
        Right t' -> leaveEff (runEitherDef (typeOf [] t')) `shouldBe` Right expected
    it "λz:ZZ. λy:YY. z (y true)" $ do
      let t = AbstractionTerm (#name @= "z" <: #type @= VariableType "ZZ" <: #body @= AbstractionTerm (#name @= "y" <: #type @= VariableType "YY" <: #body @= ApplicationTerm (#function @= VariableTerm "z" <: #argument @= ApplicationTerm (#function @= VariableTerm "y" <: #argument @= TRUE <: nil) <: nil) <: nil) <: nil)
          expected = ArrowType (#domain @= ArrowType (#domain @= VariableType "?X_0" <: #codomain @= VariableType "?X_1" <: nil) <: #codomain @= ArrowType (#domain @= ArrowType (#domain @= BoolType <: #codomain @= VariableType "?X_0" <: nil) <: #codomain @= VariableType "?X_1" <: nil) <: nil)
      case leaveUnName [] t of
        Left e -> expectationFailure $ show e
        Right t' -> leaveEff (runEitherDef (typeOf [] t')) `shouldBe` Right expected
    it "λw:W. if true then false else w false" $ do
      let t = AbstractionTerm (#name @= "w" <: #type @= VariableType "W" <: #body @= If (#cond @= TRUE <: #then @= FALSE <: #else @= ApplicationTerm (#function @= VariableTerm "w" <: #argument @= FALSE <: nil) <: nil) <: nil)
          expected = ArrowType (#domain @= ArrowType (#domain @= BoolType <: #codomain @= BoolType <: nil) <: #codomain @= BoolType <: nil)
      case leaveUnName [] t of
        Left e -> expectationFailure $ show e
        Right t' -> leaveEff (runEitherDef (typeOf [] t')) `shouldBe` Right expected
    it "let polymorphism" $ do
      let t = LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "x" <: #body @= PairTerm (VariableTerm "x") (VariableTerm "x") <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "x" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= ApplicationTerm (#function @= VariableTerm "x" <: #argument @= ImplicitAbstractionTerm (#name @= "x" <: #body @= VariableTerm "x" <: nil) <: nil) <: nil) <: nil) <: nil) <: nil) <: nil) <: nil)
          expected = NatType
      case leaveUnName [] t of
        Left e -> expectationFailure $ show e
        Right t' -> leaveEff (runEitherDef (typeOf [] t')) `shouldBe` Right expected