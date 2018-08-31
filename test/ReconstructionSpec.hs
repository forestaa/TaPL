{-# LANGUAGE OverloadedLabels #-}

module ReconstructionSpec where

import Test.Hspec
import TaPL.Reconstruction

import RIO
import qualified RIO.Map as Map
import qualified RIO.Set as Set
import qualified RIO.Text as Text

import Data.Extensible
import Data.Extensible.Effect.Default

import System.IO


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
      case leaveEff . runEitherDef $ unify' expectedconstraints of
        Left e -> expectationFailure $ show e
        Right unifier -> case leaveUnName ctx t of
          Left _ -> expectationFailure "panic"
          Right t' -> leaveReconstruction ctx t' `shouldBe` Right (instantiate unifier expectedty)
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
      leaveEff (runEitherDef $ unify' c) `shouldBe` Left (ConstraintsConflict [(NatType, ArrowType (#domain @= NatType <: #codomain @= VariableType "X" <: nil))])
    it "exercise 22.4.3 5" $ do
      let c = [(VariableType "X", ArrowType (#domain @= NatType <: #codomain @= VariableType "X" <: nil))]
      leaveEff (runEitherDef $ unify'  c) `shouldBe` Left (ConstraintsConflict [(VariableType "X", ArrowType (#domain @= NatType <: #codomain @= VariableType "X" <: nil))])
    it "exercise 22.4.3 6" $ do
      let c = []
      leaveEff (runEitherDef $ unify' c) `shouldBe` Right Map.empty
  describe "freeVariable" $
    it "λx. x" $ do
      let t = ImplicitAbstractionTerm (#name @= "x" <: #body @= VariableTerm "x" <: nil)
          Right ty = typeOf' [] t
      leaveEff (runReaderDef (freeVariable ty) []) `shouldBe` ["?X_0"]
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
    it "let f0 = λx.(x,x) in let f1 = λy.f0 (f0 y) in f1 (λz.z)" $ do
      let t = LetTerm (#name @= "f0" <: #body @= ImplicitAbstractionTerm (#name @= "x" <: #body @= PairTerm (VariableTerm "x") (VariableTerm "x") <: nil) <: #in @= LetTerm (#name @= "f1" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "f0" <: #argument @= ApplicationTerm (#function @= VariableTerm "f0" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= ApplicationTerm (#function @= VariableTerm "f1" <: #argument @= ImplicitAbstractionTerm (#name @= "z" <: #body @= VariableTerm "z" <: nil) <: nil) <: nil) <: nil)
          expected = PairType (PairType (ArrowType (#domain @= VariableType "?X_7" <: #codomain @= VariableType "?X_7" <: nil)) (ArrowType (#domain @= VariableType "?X_7" <: #codomain @= VariableType "?X_7" <: nil))) (PairType (ArrowType (#domain @= VariableType "?X_7" <: #codomain @= VariableType "?X_7" <: nil)) (ArrowType (#domain @= VariableType "?X_7" <: #codomain @= VariableType "?X_7" <: nil)))
      case leaveUnName [] t of
        Left e -> expectationFailure $ show e
        Right t' -> leaveEff (runEitherDef (typeOf [] t')) `shouldBe` Right expected
    it "let f0 = λx.(x,x) in let f1 = λy.f0 (f0 y) in let f2 = λy.f1 (f1 y) in f2 (λz.z)" $ do
      let t = LetTerm (#name @= "f0" <: #body @= ImplicitAbstractionTerm (#name @= "x" <: #body @= PairTerm (VariableTerm "x") (VariableTerm "x") <: nil) <: #in @= LetTerm (#name @= "f1" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "f0" <: #argument @= ApplicationTerm (#function @= VariableTerm "f0" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= LetTerm (#name @= "f2" <: #body @= ImplicitAbstractionTerm (#name @= "y" <: #body @= ApplicationTerm (#function @= VariableTerm "f1" <: #argument @= ApplicationTerm (#function @= VariableTerm "f1" <: #argument @= VariableTerm "y" <: nil) <: nil) <: nil) <: #in @= ApplicationTerm (#function @= VariableTerm "f2" <: #argument @= ImplicitAbstractionTerm (#name @= "z" <: #body @= VariableTerm "z" <: nil) <: nil) <: nil) <: nil) <: nil)
          expected = PairType (PairType (PairType (PairType (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)) (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil))) (PairType (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)) (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)))) (PairType (PairType (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)) (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil))) (PairType (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)) (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil))))) (PairType (PairType (PairType (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)) (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil))) (PairType (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)) (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)))) (PairType (PairType (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)) (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil))) (PairType (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)) (ArrowType (#domain @= VariableType "?X_12" <: #codomain @= VariableType "?X_12" <: nil)))))
      case leaveUnName [] t of
        Left e -> expectationFailure $ show e
        Right t' -> leaveEff (runEitherDef (typeOf [] t')) `shouldBe` Right expected