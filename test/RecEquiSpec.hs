{-# LANGUAGE OverloadedLabels #-}

module RecEquiSpec (spec) where

import Test.Hspec
import TaPL.RecEqui

import RIO
import qualified RIO.Set as Set
import qualified RIO.Vector as V

import Control.Lens ((#))
import Data.Extensible
import Data.Extensible.Effect.Default

spec :: Spec
spec = do
  describe "show Type" $ do
    it "show primitive type" $ do
      let ty = PrimitiveType "Int" :: NamedType
      show ty `shouldBe` "Int"
    it "show variable" $ do
      let ty = VariableType $ #id @= "X" <: nil :: NamedType
      show ty `shouldBe` "X"
    it "show arrow type" $ do
      let ty = VariableType $ #id @= "X" <: nil :: NamedType
          ty' = ArrowType $ #domain @= ty <: #codomain @= ty <: nil :: NamedType
      show ty' `shouldBe` "(X -> X)"
    it "show recursion type" $ do
      let ty = VariableType $ #id @= "X" <: nil :: NamedType
          ty' = RecursionType $ #name @= "X" <: #body @= ty <: nil :: NamedType
      show ty' `shouldBe` "(μX.X)"
  describe "show Term" $ do
    it "show variable term" $ do
      let t = VariableTerm $ #id @= "x" <: nil :: NamedTerm
      show t `shouldBe` "x"
    it "show abstraction term" $ do
      let t = VariableTerm $ #id @= "x" <: nil :: NamedTerm
          ty = VariableType $ #id @= "X" <: nil :: NamedType
          t' = AbstractionTerm $ #name @= "x" <: #type @= ty <: #body @= t <: nil :: NamedTerm
      show t' `shouldBe` "(λx:X.x)"
  describe "UnName" $ do
    it "μX.X" $ do
      let ty = VariableType $ #id @= "X" <: nil
          ty' = RecursionType $ #name @= "X" <: #body @= ty <: nil
          expected = RecursionType $ #name @= "X" <: #body @= VariableType (#id @= 0 <: nil) <: nil
      leaveEitherDefEvalStateDef [] (unName ty') `shouldBe` Right expected
    it "λx:X.x" $ do
      let t = VariableTerm $ #id @= "x" <: nil
          ty = PrimitiveType "X"
          t' = AbstractionTerm $ #name @= "x" <: #type @= ty <: #body @= t <: nil
          ty' = PrimitiveType "X"
          t'' = VariableTerm $ #id @= 0 <: nil
          expected = AbstractionTerm $ #name @= "x" <: #type @= ty' <: #body @= t'' <: nil
      leaveEitherDefEvalStateDef [] (unName t') `shouldBe` Right expected  
    it "μA.A->T" $ do
      let ctx = [("T", VariableTypeBind)]
          s   = RecursionType $ #name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= "A" <: nil) <: #codomain @= PrimitiveType "T" <: nil) <: nil
          expected = RecursionType $ #name @= "A" <: #body @=  ArrowType (#domain @= VariableType (#id @= 0 <: nil) <: #codomain @= PrimitiveType "T" <: nil) <: nil
      leaveEitherDefEvalStateDef ctx (unName s) `shouldBe` Right expected
    it "A->T" $ do
      let ctx = [("A", VariableTypeBind), ("T", VariableTypeBind)]
          t   = ArrowType $ #domain @= VariableType (#id @= "A" <: nil) <: #codomain @= PrimitiveType "T" <: nil
          expected = ArrowType $ #domain @= VariableType (#id @= 0 <: nil) <: #codomain @= PrimitiveType "T" <: nil
      leaveEitherDefEvalStateDef ctx (unName t) `shouldBe` Right expected
  describe "restoreName" $ do
    it "μX.X" $ do
      let ty = VariableType $ #id @= 0 <: nil
          ty' = RecursionType $ #name @= "X" <: #body @= ty <: nil
          expected = RecursionType $ #name @= "X" <: #body @=  VariableType (#id @= "X" <: nil) <: nil
      leaveEitherDefEvalStateDef [] (restoreName ty') `shouldBe` Right expected
    it "λx:X.x" $ do
      let t = VariableTerm $ #id @= 0 <: nil
          ty = PrimitiveType "X"
          t' = AbstractionTerm $ #name @= "x" <: #type @= ty <: #body @= t <: nil
          ty' = PrimitiveType "X"
          t'' = VariableTerm $ #id @= "x" <: nil
          expected = AbstractionTerm $ #name @= "x" <: #type @= ty' <: #body @= t'' <: nil
      leaveEitherDefEvalStateDef [] (restoreName t') `shouldBe` Right expected
    it "μA.A->T" $ do
      let ctx = [("T", VariableTypeBind)]
          s = RecursionType $ #name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= 0 <: nil) <: #codomain @= PrimitiveType "T" <: nil) <: nil
          expected = RecursionType $ #name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= "A" <: nil) <: #codomain @= PrimitiveType "T" <: nil) <: nil
      leaveEitherDefEvalStateDef ctx (restoreName s) `shouldBe` Right expected
    it "A->T" $ do
      let ctx = [("A", VariableTypeBind), ("T", VariableTypeBind)]
          t   = ArrowType $ #domain @= VariableType (#id @= 0 <: nil) <: #codomain @= PrimitiveType "T" <: nil
          expected = ArrowType $ #domain @= VariableType (#id @= "A" <: nil) <: #codomain @= PrimitiveType "T" <: nil
      leaveEitherDefEvalStateDef ctx (restoreName t) `shouldBe` Right expected
  describe "substitution" $
    it "subst μA.A->T A->T" $ do
      let ctx = [("A", VariableTypeBind), ("T", VariableTypeBind)]
          s   = RecursionType $ #name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= "A" <: nil) <: #codomain @= PrimitiveType "T" <: nil) <: nil
          t   = ArrowType $ #domain @= VariableType (#id @= "A" <: nil) <: #codomain @= PrimitiveType "T" <: nil
      case (leaveEitherDefEvalStateDef ctx $ unName s, leaveEitherDefEvalStateDef ctx $ unName t) of
        (Right s', Right t') -> do
          let ret = betaReduction s' t'
              expected = ArrowType $ #domain @= RecursionType (#name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= "A" <: nil) <: #codomain @= PrimitiveType "T" <: nil) <: nil) <: #codomain @= PrimitiveType "T" <: nil
          leaveEitherDefEvalStateDef ctx (restoreName ret) `shouldBe` Right expected
        _ -> expectationFailure "panic"
  describe "typeOf" $ do
    it "fix = fλ:T->T. (λx:μA.A->T. f (x x)) (λx:μA.A->T. f (x x))" $ do
      let ctx = [("T", VariableTypeBind)]
          t   = AbstractionTerm $ #name @= "x" <: #type @= RecursionType (#name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= "A" <: nil) <: #codomain @= PrimitiveType "T" <: nil) <: nil) <: #body @= ApplicationTerm (#function @= VariableTerm (#id @= "f" <: nil) <: #argument @= ApplicationTerm (#function @= VariableTerm (#id @= "x" <: nil) <: #argument @= VariableTerm (#id @= "x" <: nil) <: nil) <: nil) <: nil :: NamedTerm
          fix = AbstractionTerm $ #name @= "f" <: #type @= ArrowType (#domain @= PrimitiveType "T" <: #codomain @= PrimitiveType "T" <: nil) <: #body @= ApplicationTerm (#function @= t <: #argument @= t <: nil) <: nil :: NamedTerm
          expected = ArrowType $ #domain @= ArrowType (#domain @= PrimitiveType "T" <: #codomain @= PrimitiveType "T" <: nil) <: #codomain @= PrimitiveType "T" <: nil
      case leaveEitherDefEvalStateDef ctx (unName fix) of
        Right fix' -> leaveEitherDefEvalStateDef ctx (typeOf fix') `shouldBe` Right expected
        _ -> expectationFailure "panic"
    it "hungry" $ do
      let hungry = RecursionType $ #name @= "A" <: #body @= ArrowType (#domain @= PrimitiveType "T" <: #codomain @= VariableType (#id @= "A" <: nil) <: nil) <: nil :: NamedType
          ty = ArrowType $ #domain @= PrimitiveType "T" <: #codomain @= ArrowType (#domain @= PrimitiveType "T" <: #codomain @= hungry <: nil) <: nil :: NamedType
          fixty = ArrowType $ #domain @= ArrowType (#domain @= ty <: #codomain @= ty <: nil) <: #codomain @= ty <: nil
          ctx = [("T", VariableTypeBind)]
      case leaveEitherDefEvalStateDef ctx (unName fixty) of
        Left e -> expectationFailure $ show e
        Right fixty' -> do
          let ctx' = ("fix", VariableTermBind fixty') `V.cons` ctx
              f =  AbstractionTerm $ #name @= "f" <: #type @= ArrowType (#domain @= PrimitiveType "T" <: #codomain @= hungry <: nil) <: #body @= AbstractionTerm (#name @= "t" <: #type @= PrimitiveType "T" <: #body @= VariableTerm (#id @= "f" <: nil) <: nil) <: nil :: NamedTerm
              g = ApplicationTerm (#function @= VariableTerm (#id @= "fix" <: nil) <: #argument @= f <: nil)
              expected = ArrowType $ #domain @= PrimitiveType "T" <: #codomain @= ArrowType (#domain @= PrimitiveType "T" <: #codomain @= hungry <: nil) <: nil
          case leaveEitherDefEvalStateDef ctx' (unName g) of
            Left e-> expectationFailure $ show e
            Right g' -> 
              case leaveEitherDefEvalStateDef ctx' (typeOf g') of
                Right gty -> leaveEitherDefEvalStateDef ctx' (restoreName gty) `shouldBe` Right expected
                Left e -> expectationFailure $ show e
    it "Scott Domain: D=μX.X->X" $ do
      let scott = RecursionType $ #name @= "X" <: #body @= ArrowType (#domain @= VariableType (#id @= "X" <: nil) <: #codomain @= VariableType (#id @= "X" <: nil) <: nil) <: nil :: NamedType
          ap = AbstractionTerm $ #name @= "f" <: #type @= scott <: #body @= AbstractionTerm (#name @= "x" <: #type @= scott <: #body @= ApplicationTerm (#function @= VariableTerm (#id @= "f" <: nil) <: #argument @= VariableTerm (#id @= "x" <: nil) <: nil) <: nil) <: nil
      case leaveEitherDefEvalStateDef [] (unName ap) of
        Left e -> expectationFailure $ show e
        Right ap' -> 
          case leaveEitherDefEvalStateDef [] (typeOf ap') of
            Left e -> expectationFailure $ show e
            Right ty -> 
              case leaveEitherDefEvalStateDef [] (unName scott) of
                Right scott' -> leaveEvalStateDef Set.empty (isEquivalent scott' ty) `shouldBe` True
                Left e -> expectationFailure $ show e
    it "call by value fix = λf:(S->T)->(S->T). (λx:μA.A->S->T. f (λy:Set. (x x) y)) (λx:μA.A->S->T. f (λy:Set. (x x) y))" $ do
      let ctx = [("S", VariableTypeBind), ("T", VariableTypeBind)]
          t   = AbstractionTerm $ #name @= "x" <: #type @= RecursionType (#name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= "A" <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType "S" <: #codomain @= PrimitiveType "T" <: nil) <: nil) <: nil) <: #body @= ApplicationTerm (#function @= VariableTerm (#id @= "f" <: nil) <: #argument @= AbstractionTerm (#name @= "y" <: #type @= PrimitiveType "S" <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= VariableTerm (#id @= "x" <: nil) <: #argument @= VariableTerm (#id @= "x" <: nil) <: nil) <: #argument @= VariableTerm (#id @= "y" <: nil) <: nil) <: nil) <: nil) <: nil :: NamedTerm
          fix = AbstractionTerm $ #name @= "f" <: #type @= ArrowType (#domain @= ArrowType (#domain @= PrimitiveType "S" <: #codomain @= PrimitiveType "T" <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType "S" <: #codomain @= PrimitiveType "T" <: nil) <: nil) <: #body @= ApplicationTerm (#function @= t <: #argument @= t <: nil) <: nil :: NamedTerm
          expected = ArrowType $ #domain @= ArrowType (#domain @= ArrowType (#domain @= PrimitiveType "S" <: #codomain @= PrimitiveType "T" <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType "S" <: #codomain @= PrimitiveType "T" <: nil) <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType "S" <: #codomain @= PrimitiveType "T" <: nil) <: nil
      case leaveEitherDefEvalStateDef ctx (unName fix) of
        Right fix' -> leaveEitherDefEvalStateDef ctx (typeOf fix') `shouldBe` Right expected
        Left e -> expectationFailure $ show e
  describe "eval" $
    it "hungry 0 1 2" $ do
      let ds = [("Nat", ConstTypeDec), ("0", ConstTermDec (PrimitiveType "Nat")), ("1", ConstTermDec (PrimitiveType "Nat")), ( "2", ConstTermDec (PrimitiveType "Nat"))]
          hungryty = RecursionType $ #name @= "A" <: #body @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= VariableType (#id @= "A" <: nil) <: nil) <: nil :: NamedType
          t   = AbstractionTerm $ #name @= "x" <: #type @= RecursionType (#name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= "A" <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= hungryty <: nil) <: nil) <: nil) <: #body @= ApplicationTerm (#function @= VariableTerm (#id @= "f" <: nil) <: #argument @= AbstractionTerm (#name @= "y" <: #type @= PrimitiveType "Nat" <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= VariableTerm (#id @= "x" <: nil) <: #argument @= VariableTerm (#id @= "x" <: nil) <: nil) <: #argument @= VariableTerm (#id @= "y" <: nil) <: nil) <: nil) <: nil) <: nil :: NamedTerm
          fix = AbstractionTerm $ #name @= "f" <: #type @= ArrowType (#domain @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= hungryty <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= hungryty <: nil) <: nil) <: #body @= ApplicationTerm (#function @= t <: #argument @= t <: nil) <: nil :: NamedTerm
          natToHungry = ArrowType $ #domain @= PrimitiveType "Nat" <: #codomain @= hungryty <: nil :: NamedType
          f =  AbstractionTerm $ #name @= "f" <: #type @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= hungryty <: nil) <: #body @= AbstractionTerm (#name @= "t" <: #type @= PrimitiveType "Nat" <: #body @= VariableTerm (#id @= "f" <: nil) <: nil) <: nil :: NamedTerm
          hungry = ApplicationTerm (#function @= fix <: #argument @= f <: nil)
          term = ApplicationTerm $ #function @= ApplicationTerm (#function @= ApplicationTerm (#function @= hungry <: #argument @= ConstTerm "0" <: nil) <: #argument @= ConstTerm "1" <: nil) <: #argument @= ConstTerm "2" <: nil
          t' = AbstractionTerm (#name @= "x" <: #type @= RecursionType (#name @= "A" <: #body @= ArrowType (#domain @= VariableType (#id @= "A" <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= RecursionType (#name @= "A" <: #body @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= VariableType (#id @= "A" <: nil) <: nil) <: nil) <: nil) <: nil) <: nil) <: #body @= ApplicationTerm (#function @= AbstractionTerm (#name @= "f" <: #type @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= RecursionType (#name @= "A" <: #body @= ArrowType (#domain @= PrimitiveType "Nat" <: #codomain @= VariableType (#id @= "A" <: nil) <: nil) <: nil)  <: nil) <: #body @= AbstractionTerm (#name @= "t" <: #type @= PrimitiveType "Nat" <: #body @= VariableTerm (#id @= "f" <: nil) <: nil) <: nil) <: #argument @= AbstractionTerm (#name @= "y" <: #type @= PrimitiveType "Nat" <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= VariableTerm (#id @= "x" <: nil) <: #argument @= VariableTerm (#id @= "x" <: nil) <: nil) <: #argument @= VariableTerm (#id @= "y" <: nil) <: nil) <: nil) <: nil) <: nil)
          expectedTerm = AbstractionTerm $ #name @= "y" <: #type @= PrimitiveType "Nat" <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= t' <: #argument @= t' <: nil) <: #argument @= VariableTerm (#id @= "y" <: nil) <: nil) <:nil
      case eval ds term of
        Right (t, ty) -> do
          t `shouldBe` expectedTerm
          isEquivalentNamedFromDeclarations ds ty hungryty `shouldBe` Right True
        Left e -> expectationFailure $ show e