{-# LANGUAGE OverloadedLabels #-}

module RecEquiSpec (spec) where

import Test.Hspec
import TaPL.RecEqui

import qualified Data.Set as S
import Control.Lens ((#))
import Data.Extensible
import Data.Extensible.Effect.Default

spec :: Spec
spec = do
  describe "show Type" $ do
    it "show primitive type" $ do
      let ty = PrimitiveType $ SString "Int" :: NamedType
      show ty `shouldBe` "Int"
    it "show variable" $ do
      let ty = VariableType $ #id @= SString "X" <: nil :: NamedType
      show ty `shouldBe` "X"
    it "show arrow type" $ do
      let ty = VariableType $ #id @= SString "X" <: nil :: NamedType
          ty' = ArrowType $ #domain @= ty <: #codomain @= ty <: nil :: NamedType
      show ty' `shouldBe` "(X -> X)"
    it "show recursion type" $ do
      let ty = VariableType $ #id @= SString "X" <: nil :: NamedType
          ty' = RecursionType $ #name @= SString "X" <: #body @= ty <: nil :: NamedType
      show ty' `shouldBe` "(μX.X)"
  describe "show Term" $ do
    it "show variable term" $ do
      let t = VariableTerm $ #id @= SString "x" <: nil :: NamedTerm
      show t `shouldBe` "x"
    it "show abstraction term" $ do
      let t = VariableTerm $ #id @= SString "x" <: nil :: NamedTerm
          ty = VariableType $ #id @= SString "X" <: nil :: NamedType
          t' = AbstractionTerm $ #name @= SString "x" <: #type @= ty <: #body @= t <: nil :: NamedTerm
      show t' `shouldBe` "(λx:X.x)"
  describe "UnName" $ do
    it "μX.X" $ do
      let ty = VariableType $ #id @= SString "X" <: nil
          ty' = RecursionType $ #name @= SString "X" <: #body @= ty <: nil
          expected = RecursionType $ #name @= SString "X" <: #body @= VariableType (#id @= 0 <: nil) <: nil
      leaveEitherDefEvalStateDef [] (unName ty') `shouldBe` Right expected
    it "λx:X.x" $ do
      let t = VariableTerm $ #id @= SString "x" <: nil
          ty = PrimitiveType $ SString "X"
          t' = AbstractionTerm $ #name @= SString "x" <: #type @= ty <: #body @= t <: nil
          ty' = PrimitiveType $ SString "X"
          t'' = VariableTerm $ #id @= 0 <: nil
          expected = AbstractionTerm $ #name @= SString "x" <: #type @= ty' <: #body @= t'' <: nil
      leaveEitherDefEvalStateDef [] (unName t') `shouldBe` Right expected  
    it "μA.A->T" $ do
      let ctx = [(SString "T", VariableTypeBind)]
          s   = RecursionType $ #name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil
          expected = RecursionType $ #name @= SString "A" <: #body @=  ArrowType (#domain @= VariableType (#id @= 0 <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil
      leaveEitherDefEvalStateDef ctx (unName s) `shouldBe` Right expected
    it "A->T" $ do
      let ctx = [(SString "A", VariableTypeBind), (SString "T", VariableTypeBind)]
          t   = ArrowType $ #domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil
          expected = ArrowType $ #domain @= VariableType (#id @= 0 <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil
      leaveEitherDefEvalStateDef ctx (unName t) `shouldBe` Right expected
  describe "restoreName" $ do
    it "μX.X" $ do
      let ty = VariableType $ #id @= 0 <: nil
          ty' = RecursionType $ #name @= SString "X" <: #body @= ty <: nil
          expected = RecursionType $ #name @= SString "X" <: #body @=  VariableType (#id @= SString "X" <: nil) <: nil
      leaveEvalStateDef [] (restoreName ty') `shouldBe` expected
    it "λx:X.x" $ do
      let t = VariableTerm $ #id @= 0 <: nil
          ty = PrimitiveType $ SString "X"
          t' = AbstractionTerm $ #name @= SString "x" <: #type @= ty <: #body @= t <: nil
          ty' = PrimitiveType $ SString "X"
          t'' = VariableTerm $ #id @= SString "x" <: nil
          expected = AbstractionTerm $ #name @= SString "x" <: #type @= ty' <: #body @= t'' <: nil
      leaveEvalStateDef [] (restoreName t') `shouldBe` expected
    it "μA.A->T" $ do
      let ctx = [(SString "T", VariableTypeBind)]
          s = RecursionType $ #name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= 0 <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil
          expected = RecursionType $ #name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil
      leaveEvalStateDef ctx (restoreName s) `shouldBe` expected
    it "A->T" $ do
      let ctx = [(SString "A", VariableTypeBind), (SString "T", VariableTypeBind)]
          t   = ArrowType $ #domain @= VariableType (#id @= 0 <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil
          expected = ArrowType $ #domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil
      leaveEvalStateDef ctx (restoreName t) `shouldBe` expected
  describe "substitution" $
    it "subst μA.A->T A->T" $ do
      let ctx = [(SString "A", VariableTypeBind), (SString "T", VariableTypeBind)]
          s   = RecursionType $ #name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil
          t   = ArrowType $ #domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil
      case (leaveEitherDefEvalStateDef ctx $ unName s, leaveEitherDefEvalStateDef ctx $ unName t) of
        (Right s', Right t') -> do
          let ret = betaReduction s' t'
              expected = ArrowType $ #domain @= RecursionType (#name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil
          leaveEvalStateDef ctx (restoreName ret) `shouldBe` expected
        _ -> expectationFailure "panic"
  describe "typeOf" $ do
    it "fix = fλ:T->T. (λx:μA.A->T. f (x x)) (λx:μA.A->T. f (x x))" $ do
      let ctx = [(SString "T", VariableTypeBind)]
          t   = AbstractionTerm $ #name @= SString "x" <: #type @= RecursionType (#name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil) <: #body @= ApplicationTerm (#function @= VariableTerm (#id @= SString "f" <: nil) <: #argument @= ApplicationTerm (#function @= VariableTerm (#id @= SString "x" <: nil) <: #argument @= VariableTerm (#id @= SString "x" <: nil) <: nil) <: nil) <: nil :: NamedTerm
          fix = AbstractionTerm $ #name @= SString "f" <: #type @= ArrowType (#domain @= PrimitiveType (SString "T") <: #codomain @= PrimitiveType (SString "T") <: nil) <: #body @= ApplicationTerm (#function @= t <: #argument @= t <: nil) <: nil :: NamedTerm
          expected = ArrowType $ #domain @= ArrowType (#domain @= PrimitiveType (SString "T") <: #codomain @= PrimitiveType (SString "T") <: nil) <: #codomain @= PrimitiveType (SString "T") <: nil
      case leaveEitherDefEvalStateDef ctx (unName fix) of
        Right fix' -> leaveEitherDefEvalStateDef ctx (typeOf fix') `shouldBe` Right expected
        _ -> expectationFailure "panic"
    it "hungry" $ do
      let hungry = RecursionType $ #name @= SString "A" <: #body @= ArrowType (#domain @= PrimitiveType (SString "T") <: #codomain @= VariableType (#id @= SString "A" <: nil) <: nil) <: nil :: NamedType
          ty = ArrowType $ #domain @= PrimitiveType (SString "T") <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "T") <: #codomain @= hungry <: nil) <: nil :: NamedType
          fixty = ArrowType $ #domain @= ArrowType (#domain @= ty <: #codomain @= ty <: nil) <: #codomain @= ty <: nil
          ctx = [(SString "T", VariableTypeBind)]
      case leaveEitherDefEvalStateDef ctx (unName fixty) of
        Right fixty' -> do
          let ctx' = (SString "fix", VariableTermBind fixty') : ctx
              f =  AbstractionTerm $ #name @= SString "f" <: #type @= ArrowType (#domain @= PrimitiveType (SString "T") <: #codomain @= hungry <: nil) <: #body @= AbstractionTerm (#name @= SString "t" <: #type @= PrimitiveType (SString "T") <: #body @= VariableTerm (#id @= SString "f" <: nil) <: nil) <: nil :: NamedTerm
              g = ApplicationTerm (#function @= VariableTerm (#id @= SString "fix" <: nil) <: #argument @= f <: nil)
              expected = ArrowType $ #domain @= PrimitiveType (SString "T") <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "T") <: #codomain @= hungry <: nil) <: nil
          case leaveEitherDefEvalStateDef ctx' (unName g) of
            Right g' -> 
              case leaveEitherDefEvalStateDef ctx' (typeOf g') of
                Right gty -> leaveEvalStateDef ctx' (restoreName gty) `shouldBe` expected
                Left e -> expectationFailure $ show e
            Left e-> expectationFailure $ show e
        Left e -> expectationFailure $ show e
    it "Scott Domain: D=μX.X->X" $ do
      let scott = RecursionType $ #name @= SString "X" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "X" <: nil) <: #codomain @= VariableType (#id @= SString "X" <: nil) <: nil) <: nil :: NamedType
          ap = AbstractionTerm $ #name @= SString "f" <: #type @= scott <: #body @= AbstractionTerm (#name @= SString "x" <: #type @= scott <: #body @= ApplicationTerm (#function @= VariableTerm (#id @= SString "f" <: nil) <: #argument @= VariableTerm (#id @= SString "x" <: nil) <: nil) <: nil) <: nil
      case leaveEitherDefEvalStateDef [] (unName ap) of
        Right ap' -> 
          case leaveEitherDefEvalStateDef [] (typeOf ap') of
            Right ty -> 
              case leaveEitherDefEvalStateDef [] (unName scott) of
                Right scott' -> leaveEvalStateDef S.empty (isEquivalent scott' ty) `shouldBe` True
                Left e -> expectationFailure $ show e
            Left e -> expectationFailure $ show e
        Left e -> expectationFailure $ show e
    it "call by value fix = λf:(S->T)->(S->T). (λx:μA.A->S->T. f (λy:S. (x x) y)) (λx:μA.A->S->T. f (λy:S. (x x) y))" $ do
      let ctx = [(SString "S", VariableTypeBind), (SString "T", VariableTypeBind)]
          t   = AbstractionTerm $ #name @= SString "x" <: #type @= RecursionType (#name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "S") <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil) <: nil) <: #body @= ApplicationTerm (#function @= VariableTerm (#id @= SString "f" <: nil) <: #argument @= AbstractionTerm (#name @= SString "y" <: #type @= PrimitiveType (SString "S") <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= VariableTerm (#id @= SString "x" <: nil) <: #argument @= VariableTerm (#id @= SString "x" <: nil) <: nil) <: #argument @= VariableTerm (#id @= SString "y" <: nil) <: nil) <: nil) <: nil) <: nil :: NamedTerm
          fix = AbstractionTerm $ #name @= SString "f" <: #type @= ArrowType (#domain @= ArrowType (#domain @= PrimitiveType (SString "S") <: #codomain @= PrimitiveType (SString "T") <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "S") <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil) <: #body @= ApplicationTerm (#function @= t <: #argument @= t <: nil) <: nil :: NamedTerm
          expected = ArrowType $ #domain @= ArrowType (#domain @= ArrowType (#domain @= PrimitiveType (SString "S") <: #codomain @= PrimitiveType (SString "T") <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "S") <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "S") <: #codomain @= PrimitiveType (SString "T") <: nil) <: nil
      case leaveEitherDefEvalStateDef ctx (unName fix) of
        Right fix' -> leaveEitherDefEvalStateDef ctx (typeOf fix') `shouldBe` Right expected
        Left e -> expectationFailure $ show e
  describe "eval" $
    it "hungry 0 1 2" $ do
      let ds = [(SString "Nat", ConstTypeDec), (SString "0", ConstTermDec (PrimitiveType (SString "Nat"))), (SString "1", ConstTermDec (PrimitiveType (SString "Nat"))), (SString "2", ConstTermDec (PrimitiveType (SString "Nat")))]
          hungryty = RecursionType $ #name @= SString "A" <: #body @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= VariableType (#id @= SString "A" <: nil) <: nil) <: nil :: NamedType
          t   = AbstractionTerm $ #name @= SString "x" <: #type @= RecursionType (#name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= hungryty <: nil) <: nil) <: nil) <: #body @= ApplicationTerm (#function @= VariableTerm (#id @= SString "f" <: nil) <: #argument @= AbstractionTerm (#name @= SString "y" <: #type @= PrimitiveType (SString "Nat") <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= VariableTerm (#id @= SString "x" <: nil) <: #argument @= VariableTerm (#id @= SString "x" <: nil) <: nil) <: #argument @= VariableTerm (#id @= SString "y" <: nil) <: nil) <: nil) <: nil) <: nil :: NamedTerm
          fix = AbstractionTerm $ #name @= SString "f" <: #type @= ArrowType (#domain @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= hungryty <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= hungryty <: nil) <: nil) <: #body @= ApplicationTerm (#function @= t <: #argument @= t <: nil) <: nil :: NamedTerm
          natToHungry = ArrowType $ #domain @= PrimitiveType (SString "Nat") <: #codomain @= hungryty <: nil :: NamedType
          f =  AbstractionTerm $ #name @= SString "f" <: #type @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= hungryty <: nil) <: #body @= AbstractionTerm (#name @= SString "t" <: #type @= PrimitiveType (SString "Nat") <: #body @= VariableTerm (#id @= SString "f" <: nil) <: nil) <: nil :: NamedTerm
          hungry = ApplicationTerm (#function @= fix <: #argument @= f <: nil)
          term = ApplicationTerm $ #function @= ApplicationTerm (#function @= ApplicationTerm (#function @= hungry <: #argument @= ConstTerm (SString "0") <: nil) <: #argument @= ConstTerm (SString "1") <: nil) <: #argument @= ConstTerm (SString "2") <: nil
          t' = AbstractionTerm (#name @= SString "x" <: #type @= RecursionType (#name @= SString "A" <: #body @= ArrowType (#domain @= VariableType (#id @= SString "A" <: nil) <: #codomain @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= RecursionType (#name @= SString "A" <: #body @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= VariableType (#id @= SString "A" <: nil) <: nil) <: nil) <: nil) <: nil) <: nil) <: #body @= ApplicationTerm (#function @= AbstractionTerm (#name @= SString "f" <: #type @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= RecursionType (#name @= SString "A" <: #body @= ArrowType (#domain @= PrimitiveType (SString "Nat") <: #codomain @= VariableType (#id @= SString "A" <: nil) <: nil) <: nil)  <: nil) <: #body @= AbstractionTerm (#name @= SString "t" <: #type @= PrimitiveType (SString "Nat") <: #body @= VariableTerm (#id @= SString "f" <: nil) <: nil) <: nil) <: #argument @= AbstractionTerm (#name @= SString "y" <: #type @= PrimitiveType (SString "Nat") <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= VariableTerm (#id @= SString "x" <: nil) <: #argument @= VariableTerm (#id @= SString "x" <: nil) <: nil) <: #argument @= VariableTerm (#id @= SString "y" <: nil) <: nil) <: nil) <: nil) <: nil)
          expected = AbstractionTerm $ #name @= SString "y" <: #type @= PrimitiveType (SString "Nat") <: #body @= ApplicationTerm (#function @= ApplicationTerm (#function @= t' <: #argument @= t' <: nil) <: #argument @= VariableTerm (#id @= SString "y" <: nil) <: nil) <:nil
      eval ds term `shouldBe` Right expected