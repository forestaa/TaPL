{-# LANGUAGE OverloadedLabels #-}

module SystemFOmegaSubSpec (spec) where

import Test.Hspec
import TaPL.SystemFOmegaSub

import TaPL.NameLess
import SString

import RIO
import qualified RIO.Vector as V

import Control.Monad.State.Strict
import Data.Extensible


spec :: Spec
spec = do
  describe "unName/restoreName" $ do
    it "λX.X ---> λX.0" $ do
      let ty = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType "X" <: nil)
          expected = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType 0 <: nil)
      leaveUnName ([] :: TypingContext) ty `shouldBe` Right expected
    it "λX.0 ---> λX.X" $ do
      let ty = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType 0 <: nil)
          expected = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType "X" <: nil)
      leaveRestoreName ([] :: TypingContext) ty `shouldBe` Right expected
    it "λX.∀Y<:X.Y" $ do
      let ty = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= UniversalType (#name @= "Y" <: #bound @= VariableType "X" <: #body @= VariableType "Y" <: nil) <: nil)
          expected = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= UniversalType (#name @= "Y" <: #bound @= VariableType 0 <: #body @= VariableType 0 <: nil) <: nil)
      leaveUnName ([] :: TypingContext) ty `shouldBe` Right expected
    it "λX.(λY.X->Y Top) Top" $ do
      let ty = ApplicationType (#function @= AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ApplicationType (#function @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil) <: nil) <: #argument @= TopType <: nil) <: nil) <: #argument @= TopType <: nil)
          expected = ApplicationType (#function @= AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ApplicationType (#function @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= VariableType 1 <: #codomain @= VariableType 0 <: nil) <: nil) <: #argument @= TopType <: nil) <: nil) <: #argument @= TopType <: nil)
      leaveUnName ([] :: TypingContext) ty `shouldBe` Right expected
  describe "normalize" $ do
    it "λX.(λY.X->Y Top) Top ---> Top -> Top" $ do
      let ty = ApplicationType (#function @= AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ApplicationType (#function @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil) <: nil) <: #argument @= TopType <: nil) <: nil) <: #argument @= TopType <: nil)
          expected = ArrowType (#domain @= TopType <: #codomain @= TopType <: nil)
      leaveNormalize ([] :: TypingContext) ty `shouldBe` Right expected
    it "λX.(λY.X->Y Top) --> λX.(λY.X->Y Top)" $ do
      let ty = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ApplicationType (#function @= AbstractionType (#name @= "Y" <: #kind @= StarKind <: #body @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil) <: nil) <: #argument @= TopType <: nil) <: nil)
          expected = ty
      leaveNormalize ([] :: TypingContext) ty `shouldBe` Right expected
  describe "subtype" $ do
    let idType = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType "X" <: nil)
        idType' = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= VariableType 0 <: nil)
        ctx = [("F", VariableTypeBind idType'), ("A", VariableTypeBind (VariableType 0)), ("B", VariableTypeBind TopType)]
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
  describe "typing: chpater 32" . (`evalStateT` []) $ do
    let counter = ExistentialType (#name @= "X" <: #bound @= topOf StarKind <: #body @= RecordType [("state", (Covariant, VariableType 0)), ("methods", (Covariant, RecordType [("get", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= NatType <: nil))), ("inc", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil)))]))] <: nil)
        counterR = RecordType [("x", (Covariant, NatType))]

    modify $ V.cons ("Counter", TypeAbbreviationBind counter)
    modify $ V.cons ("CounterR", TypeAbbreviationBind counterR)
    ctx <- get

    let c = PackageTerm (#type @= VariableType "CounterR" <: #term @= RecordTerm [("state", (Covariant, RecordTerm [("x", (Covariant, Zero))])), ("methods", (Covariant, RecordTerm [("get", (Covariant, AbstractionTerm (#name @= "r" <: #type @= VariableType "CounterR" <: #body @= ProjectionTerm (#term @= VariableTerm "r" <: #label @= "x" <: nil) <: nil))), ("inc", (Covariant, AbstractionTerm (#name @= "r" <: #type @= VariableType "CounterR" <: #body @= RecordTerm [("x", (Covariant, Succ (ProjectionTerm (#term @= VariableTerm "r" <: #label @= "x" <: nil))))] <: nil)))]))] <: #exist @= VariableType "Counter" <: nil)

    lift $ it "{*CounterR, {state = {x = 0}, methods = {get = λr:CounterR. r.x, inc = λr:CounterR. {x=succ(r.x)}}}} as Counter" $ do
      let expected = VariableType "Counter"
      leaveTyping ctx c `shouldBe` Right expected

    lift $ it "sendget = λc:Counter. let {X, body} = c in body.methods.get(body.state) : Counter -> Nat" $ do
      let sendget = AbstractionTerm (#name @= "c" <: #type @= VariableType "Counter" <: #body @= UnPackageTerm (#type @= "X" <: #name @= "body" <: #body @= VariableTerm "c" <: #in @= ApplicationTerm (#function @= ProjectionTerm (#term @= ProjectionTerm (#term @= VariableTerm "body" <: #label @= "methods" <: nil) <: #label @= "get" <: nil) <: #argument @= ProjectionTerm (#term @= VariableTerm "body" <: #label @= "state" <: nil) <: nil) <: nil) <: nil)
          expected = ArrowType (#domain @= VariableType "Counter" <: #codomain @= NatType <: nil)
      leaveTyping ctx sendget `shouldBe` Right expected
      let t = ApplicationTerm (#function @= sendget <: #argument @= c <: nil)
          expected = NatType
      leaveTyping ctx t `shouldBe` Right expected

    let sendinc = AbstractionTerm (#name @= "c" <: #type @= VariableType "Counter" <: #body @= UnPackageTerm (#type @= "X" <: #name @= "body" <: #body @= VariableTerm "c" <: #in @= PackageTerm (#type @= VariableType "X" <: #term @= RecordTerm [("state", (Covariant, ApplicationTerm (#function @= ProjectionTerm (#term @= ProjectionTerm (#term @= VariableTerm "body" <: #label @= "methods" <: nil) <: #label @= "inc" <: nil) <: #argument @= ProjectionTerm (#term @= VariableTerm "body" <: #label @= "state" <: nil) <: nil))), ("methods", (Covariant, ProjectionTerm (#term @= VariableTerm "body" <: #label @= "methods" <: nil)))] <: #exist @= VariableType "Counter" <: nil) <: nil) <: nil)

    lift $ it "sendinc = λc:Counter. let {X, body} = c in {*X, {state = body.methods.inc(body.state), methods = body.methods}} as Counter : Counter -> Counter" $ do
      let expected = ArrowType (#domain @= VariableType "Counter" <: #codomain @= VariableType "Counter" <: nil)
      leaveTyping ctx sendinc `shouldBe` Right expected

    let resetCounter = ExistentialType (#name @= "X" <: #bound @= topOf StarKind <: #body @= RecordType [("state", (Covariant, VariableType 0)), ("methods", (Covariant, RecordType [("get", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= NatType <: nil))), ("inc", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil))), ("reset", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil)))]))] <: nil)

    modify $ V.cons ("ResetCounter", TypeAbbreviationBind resetCounter)
    ctx <- get

    let rc = PackageTerm (#type @= VariableType "CounterR" <: #term @= RecordTerm [("state", (Covariant, RecordTerm [("x", (Covariant, Zero))])), ("methods", (Covariant, RecordTerm [("get", (Covariant, AbstractionTerm (#name @= "r" <: #type @= VariableType "CounterR" <: #body @= ProjectionTerm (#term @= VariableTerm "r" <: #label @= "x" <: nil) <: nil))), ("inc", (Covariant, AbstractionTerm (#name @= "r" <: #type @= VariableType "CounterR" <: #body @= RecordTerm [("x", (Covariant, Succ (ProjectionTerm (#term @= VariableTerm "r" <: #label @= "x" <: nil))))] <: nil))), ("reset", (Covariant, AbstractionTerm (#name @= "r" <: #type @= VariableType "CounterR" <: #body @= RecordTerm [("x", (Covariant, Zero))] <: nil)))]))] <: #exist @= VariableType "ResetCounter" <: nil)

    lift $ it "reset counter rc = {*CounterR, {state = {x = 0}, methods = {get = λr:CounterR. r.x, inc = λr:CounterR. {x=succ(r.x)}, reset = λr:CounterR. {x=0}}}} as ResetCounter" $ do
      let expected1 = VariableType "ResetCounter"
      leaveTyping ctx rc `shouldBe` Right expected1
      let t = ApplicationTerm (#function @= sendinc <: #argument @= rc <: nil)
          expected2 = VariableType "Counter"
      leaveTyping ctx t `shouldBe` Right expected2

    let object = AbstractionType (#name @= "M" <: #kind @= ArrowKind (#domain @= StarKind <: #codomain @= StarKind <: nil) <: #body @= ExistentialType (#name @= "X" <: #bound @= TopType <: #body @= RecordType [("state", (Covariant, VariableType 0)), ("methods", (Covariant, ApplicationType (#function @= VariableType 1 <: #argument @= VariableType 0 <: nil)))] <: nil) <: nil)
        counterM = AbstractionType (#name @= "R" <: #kind @= StarKind <: #body @= RecordType [("get", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= NatType <: nil))), ("inc", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil)))] <: nil)
        
    modify $ V.cons ("Object", TypeAbbreviationBind object)
    modify $ V.cons ("CounterM", TypeAbbreviationBind counterM) 
    ctx <- get

    let sendinc' = TypeAbstractionTerm (#name @= "M" <: #bound @= VariableType "CounterM" <: #body @= AbstractionTerm (#name @= "c" <: #type @= ApplicationType (#function @= VariableType "Object" <: #argument @= VariableType "M" <: nil) <: #body @= UnPackageTerm (#type @= "X" <: #name @= "b" <: #body @= VariableTerm "c" <: #in @= PackageTerm (#type @= VariableType "X" <: #term @= RecordTerm [("state", (Covariant, ApplicationTerm (#function @= ProjectionTerm (#term @= ProjectionTerm (#term @= VariableTerm "b" <: #label @= "methods" <: nil) <: #label @= "inc" <: nil) <: #argument @= ProjectionTerm (#term @= VariableTerm "b" <: #label @= "state" <: nil) <: nil))), ("methods", (Covariant, ProjectionTerm (#term @= VariableTerm "b" <: #label @= "methods" <: nil)))] <: #exist @= ApplicationType (#function @= VariableType "Object" <: #argument @= VariableType "M" <: nil) <: nil) <: nil) <: nil) <: nil)

    lift $ it "sendinc: ∀M<:CounterM. Object M -> Object M" $ do
      let expected = UniversalType (#name @= "M" <: #bound @= VariableType "CounterM" <: #body @= ArrowType (#domain @= ApplicationType (#function @= VariableType "Object" <: #argument @= VariableType "M" <: nil) <: #codomain @= ApplicationType (#function @= VariableType "Object" <: #argument @= VariableType "M" <: nil) <: nil) <: nil)
      leaveTyping ctx sendinc' `shouldBe` Right expected

    let resetCounterM = AbstractionType (#name @= "R" <: #kind @= StarKind <: #body @= RecordType [("get", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= NatType <: nil))), ("inc", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil))), ("reset", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil)))] <: nil)
 
    modify $ V.cons ("ResetCounterM", TypeAbbreviationBind resetCounterM)
    ctx <- get

    lift $ it "sendinc [ResetConterM] rc" $ do
      let t = ApplicationTerm (#function @= TypeApplicationTerm (#term @= sendinc' <: #type @= VariableType "ResetCounterM" <: nil) <: #argument @= rc <: nil)
          expected = ApplicationType (#function @= VariableType "Object" <: #argument @= VariableType "ResetCounterM" <: nil)
      leaveTyping ctx t `shouldBe` Right expected
    
    let counterR = RecordType [("x", (Invariant, NatType))]

    put [("ResetCounterM", TypeAbbreviationBind resetCounterM), ("CounterM", TypeAbbreviationBind counterM), ("Object", TypeAbbreviationBind object), ("ResetCounter", TypeAbbreviationBind resetCounter), ("CounterR", TypeAbbreviationBind counterR), ("Counter", TypeAbbreviationBind counter)]
    ctx <- get

    let counterClass = TypeAbstractionTerm (#name @= "R" <: #bound @= VariableType "CounterR" <: #body @= AscribeTerm (#term @= RecordTerm [("get", (Covariant, AbstractionTerm (#name @= "s" <: #type @= VariableType "R" <: #body @= ProjectionTerm (#term @= VariableTerm "s" <: #label @= "x" <: nil) <: nil))), ("inc", (Covariant, AbstractionTerm (#name @= "s" <: #type @= VariableType "R" <: #body @= UpdateTerm (#record @= VariableTerm "s" <: #label @= "x" <: #new @= Succ (ProjectionTerm (#term @= VariableTerm "s" <: #label @= "x" <: nil)) <: nil) <: nil)))] <: #as @= ApplicationType (#function @= VariableType "CounterM" <: #argument @= VariableType "R" <: nil) <: nil) <: nil)

    lift $ it "CounterClass" $ do
      let expected = UniversalType (#name @= "R" <: #bound @= VariableType "CounterR" <: #body @= ApplicationType (#function @= VariableType "CounterM" <: #argument @= VariableType "R" <: nil) <: nil)
      leaveTyping ctx counterClass `shouldBe` Right expected
      -- leaveTypingAssertion ctx counterClass expected `shouldBe` Right True

    lift $ it "CounterClass instance" $ do
      let t = PackageTerm (#type @= VariableType "CounterR" <: #term @= RecordTerm [("state", (Covariant, RecordTerm [("x", (Invariant, Zero))])), ("methods", (Covariant, TypeApplicationTerm (#term @= counterClass <: #type @= VariableType "CounterR" <: nil)))] <: #exist @= ApplicationType (#function @= VariableType "Object" <: #argument @= VariableType "CounterM" <: nil) <: nil)
          expected = VariableType "Counter"
      leaveTypingAssertion ctx t expected `shouldBe` Right True

    let resetCounterClass = TypeAbstractionTerm (#name @= "R" <: #bound @= VariableType "CounterR" <: #body @= LetTerm (#name @= "super" <: #body @= TypeApplicationTerm (#term @= counterClass <: #type @= VariableType "R" <: nil) <: #in @= AscribeTerm (#term @= RecordTerm [("get", (Covariant, ProjectionTerm (#term @= VariableTerm "super" <: #label @= "get" <: nil))), ("inc", (Covariant, ProjectionTerm (#term @= VariableTerm "super" <: #label @= "inc" <: nil))), ("reset", (Covariant, AbstractionTerm (#name @= "s" <: #type @= VariableType "R" <: #body @= UpdateTerm (#record @= VariableTerm "s" <: #label @= "x" <: #new @= Zero <: nil) <: nil)))] <: #as @= ApplicationType (#function @= VariableType "ResetCounterM" <: #argument @= VariableType "R" <: nil) <: nil) <: nil) <: nil)

    lift $ it "ResetCounterClass" $ do
      let expected = UniversalType (#name @= "R" <: #bound @= VariableType "CounterR" <: #body @= ApplicationType (#function @= VariableType "ResetCounterM" <: #argument @= VariableType "R" <: nil) <: nil)
      leaveSubTypingAssertion ctx resetCounterClass expected `shouldBe` Right True

    let backupCounterM = AbstractionType (#name @= "R" <: #kind @= StarKind <: #body @= RecordType [("get", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= NatType <: nil))), ("inc", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil))), ("reset", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil))), ("backup", (Covariant, ArrowType (#domain @= VariableType 0 <: #codomain @= VariableType 0 <: nil)))] <: nil)
        backupCounterR = RecordType [("x", (Invariant, NatType)), ("old", (Invariant, NatType))]
        backupCounterClass = TypeAbstractionTerm (#name @= "R" <: #bound @= VariableType "BackupCounterR" <: #body @= LetTerm (#name @= "super" <: #body @= TypeApplicationTerm (#term @= resetCounterClass <: #type @= VariableType "R" <: nil) <: #in @= AscribeTerm (#term @= RecordTerm [("get", (Covariant, ProjectionTerm (#term @= VariableTerm "super" <: #label @= "get" <: nil))), ("inc", (Covariant, ProjectionTerm (#term @= VariableTerm "super" <: #label @= "inc" <: nil))), ("reset", (Covariant, AbstractionTerm (#name @= "s" <: #type @= VariableType "R" <: #body @= UpdateTerm (#record @= VariableTerm "s" <: #label @= "x" <: #new @= ProjectionTerm (#term @= VariableTerm "s" <: #label @= "old" <: nil) <:nil) <: nil))), ("backup", (Covariant, AbstractionTerm (#name @= "s" <: #type @= VariableType "R" <: #body @= UpdateTerm (#record @= VariableTerm "s" <: #label @= "old" <: #new @= ProjectionTerm (#term @= VariableTerm "s" <: #label @= "x" <: nil) <:nil) <: nil)))] <: #as @= ApplicationType (#function @= VariableType "BackupCounterM" <: #argument @= VariableType "R" <: nil) <: nil) <: nil) <: nil)
      
    modify $ V.cons ("BackupCounterM", TypeAbbreviationBind backupCounterM)
    modify $ V.cons ("BackupCounterR", TypeAbbreviationBind backupCounterR)
    ctx <- get

    lift $ it "BackupCounterClass" $ do
      let expected = UniversalType (#name @= "R" <: #bound @= VariableType "BackupCounterR" <: #body @= ApplicationType (#function @= VariableType "BackupCounterM" <: #argument  @= VariableType "R" <: nil) <: nil) :: NamedType
      leaveTyping ctx backupCounterClass `shouldBe` Right expected
    
  describe "Type Class" . (`evalStateT` []) $ do
    let functor = ExistentialType (#name @= "F" <: #bound @= topOf (ArrowKind (#domain @= StarKind <: #codomain @= StarKind <: nil)) <: #body @= RecordType [("fmap", (Covariant, UniversalType (#name @= "X" <: #bound @= TopType <: #body @= UniversalType (#name @= "Y" <: #bound @= TopType <: #body @= ArrowType (#domain @= ArrowType (#domain @= VariableType 1 <: #codomain @= VariableType 0 <: nil) <: #codomain @= ArrowType (#domain @= ApplicationType (#function @= VariableType 2 <: #argument @= VariableType 1 <: nil) <: #codomain @= ApplicationType (#function @= VariableType 2 <: #argument @= VariableType 0 <: nil) <: nil) <: nil) <: nil) <: nil)))] <: nil)

    modify $ V.cons ("Functor", TypeAbbreviationBind functor)
    ctx <- get

    lift $ it "Nat -> a: Functor" $ do
      let arrow = AbstractionType (#name @= "X" <: #kind @= StarKind <: #body @= ArrowType (#domain @= NatType <: #codomain @= VariableType "X" <: nil) <: nil)
          fmap = PackageTerm (#type @= arrow <: #term @= RecordTerm [("fmap", (Covariant, TypeAbstractionTerm (#name @= "X" <: #bound @= TopType <: #body @= TypeAbstractionTerm (#name @= "Y" <: #bound @= TopType <: #body @= AbstractionTerm (#name @= "f" <: #type @= ArrowType (#domain @= VariableType "X" <: #codomain @= VariableType "Y" <: nil) <: #body @= AbstractionTerm (#name @= "g" <: #type @= ArrowType (#domain @= NatType <: #codomain @= VariableType "X" <: nil) <: #body @= AbstractionTerm (#name @= "x" <: #type @= NatType <: #body @= ApplicationTerm (#function @= VariableTerm "f" <: #argument @= ApplicationTerm (#function @= VariableTerm "g" <: #argument @= VariableTerm "x" <: nil) <: nil) <: nil) <: nil) <: nil) <: nil) <: nil)))] <: #exist @= VariableType "Functor" <: nil)
          expected = VariableType "Functor"
      leaveTyping ctx fmap `shouldBe` Right expected