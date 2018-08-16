{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module TaPL.RecEqui where


import qualified Data.List as L
import Data.Proxy
import GHC.TypeLits (KnownSymbol)

import Control.Monad.Error.Class
import Control.Monad.State.Strict

import Control.Lens hiding ((:>))
import Data.Extensible
import Data.Extensible.Effect.Default



type DeBrujinIndex = Int
newtype SString = SString String deriving (Eq)
instance Show SString where
  show (SString s) = s

data A = INDEX | TYPE |TERM
type family Named (a :: A) (b :: Bool) where
  Named 'INDEX 'True  = SString
  Named 'INDEX 'False = DeBrujinIndex
  Named 'TYPE  'True  = NamedType
  Named 'TYPE  'False = UnNamedType
  Named 'TERM  'True  = NamedTerm
  Named 'TERM  'False = UnNamedTerm

class UnName (f :: Bool -> *) where
  unName :: f 'True -> Eff '[StateDef NamingContext, EitherDef Errors] (f 'False)

data family Type (a :: Bool)
newtype instance Type a = Type (Variant '["primitive" >: SString, "variable" >: VariableType a, "arrow" >: ArrowType a, "recursion" >: RecursionType a ])
newtype VariableType a = VariableType (Record '[ "id" :> Named 'INDEX a ]) 
newtype ArrowType a = ArrowType (Record '[ "domain" >: Named 'TYPE a, "codomain" >: Named 'TYPE a ])
newtype RecursionType a = RecursionType (Record '[ "name" >: SString, "body" >: Named 'TYPE a ]) 
type NamedType = Type 'True
type UnNamedType = Type 'False

data family Term (a :: Bool)
newtype instance Term a = Term (Variant '[ "variable" >: VariableTerm a, "abstraction" >: AbstractionTerm a, "application" >: ApplicationTerm a ])
newtype VariableTerm a = VariableTerm (Record '[ "id" :> Named 'INDEX a ])
newtype AbstractionTerm a = AbstractionTerm (Record '[ "name" :> SString, "type" :> Named 'TYPE a, "body" :> Named 'TERM a ])
newtype ApplicationTerm a = ApplicationTerm (Record '[ "function" :> Named 'TERM a, "argument" :> Named 'TERM a ])
type NamedTerm = Term 'True
type UnNamedTerm = Term 'False

type NamingContext = [(SString, Binding)]
data Binding = NameBind | VariableBind NamedType | TypeVariableBind deriving (Show)
type Errors = Variant '[ "removeNamesError" >: RemoveNamesError ]
newtype RemoveNamesError = RemoveNamesError (Variant '["missingVariableInNamingContext" >: Record '["name" :> SString, "namingContext" :> NamingContext] ])


instance (Show (Named 'INDEX a), Show (Named 'TYPE a)) => Show (Type a) where
  show (Type ty) = flip matchField ty $
    htabulateFor (Proxy :: Proxy (KeyValue KnownSymbol Show)) $
      \_ -> Field (Match $ show . runIdentity)
instance Show (Named 'INDEX a) => Show (VariableType a) where
  show (VariableType ty) = show (ty ^. #id)
instance Show (Named 'TYPE a) => Show (ArrowType a) where
  show (ArrowType ty) = show (ty ^. #domain) ++ " -> " ++ show (ty ^. #codomain)
instance (Show (Named 'INDEX a), Show (Named 'TYPE a)) => Show (RecursionType a) where
  show (RecursionType ty) = "(μ" ++ show (ty ^. #name) ++ "." ++ show (ty ^. #body) ++ ")"

instance (Show (Named 'INDEX a), Show (Named 'TYPE a), Show (Named 'TERM a)) => Show (Term a) where
  show (Term term) = flip matchField term $
    htabulateFor (Proxy :: Proxy (KeyValue KnownSymbol Show)) $
        \_ -> Field (Match $ show . runIdentity)
instance Show (Named 'INDEX a) => Show (VariableTerm a) where
  show (VariableTerm t) = show (t ^. #id)
instance (Show (Named 'TYPE a), Show (Named 'TERM a)) => Show (AbstractionTerm a) where
  show (AbstractionTerm t) = "(λ" ++ show (t ^. #name) ++ ":" ++ show (t ^. #type) ++ "." ++ show (t ^. #body) ++ ")"
instance  Show (Named 'TERM a) => Show (ApplicationTerm a) where
  show (ApplicationTerm t) = show (t ^. #function) ++ show (t ^. #argument)

instance Show RemoveNamesError where
  show (RemoveNamesError e) = flip matchField e $ 
      #missingVariableInNamingContext @= (\r -> concat ["missing variable in naming context: variable: ", show (r ^. #name), ", NamingContext: ", show (r ^. #namingContext)])
    <: nil



instance UnName Type where
  unName (Type ty) = flip matchField ty $
       #primitive @= return . Type . (#) #primitive
    <: #variable  @= fmap (Type . (#) #variable)  . unName
    <: #arrow     @= fmap (Type . (#) #arrow)     . unName
    <: #recursion @= fmap (Type . (#) #recursion) . unName
    <: nil
instance UnName VariableType where
  unName (VariableType ty) = do
    maybei <- gets (L.findIndex ((==) (ty ^. #id) . (^. _1)))
    case maybei of
      Just i  -> return . VariableType $ #id @= i <: nil
      Nothing -> do
        ctx <- get
        throwError $ #removeNamesError # RemoveNamesError (#missingVariableInNamingContext # (#name @= ty ^. #id <: #namingContext @= ctx <: nil))
instance UnName ArrowType where
  unName (ArrowType ty) = do
    domain <- unName $ ty ^. #domain
    codomain <- unName $ ty ^. #codomain
    return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
instance UnName RecursionType where
  unName (RecursionType ty) = do
    ctx <- get
    let x  = ty ^. #name
        body = ty ^. #body
    modify ((:) (x, TypeVariableBind))
    body' <- castEff $ evalStateDef (unName body) ctx
    return . RecursionType $ #name @= x <: #body @= body' <: nil

instance UnName Term where
  unName (Term term) = flip matchField term $
       #variable    @= fmap (Term . (#) #variable)    . unName
    <: #abstraction @= fmap (Term . (#) #abstraction) . unName
    <: #application @= fmap (Term . (#) #application) . unName
    <: nil
instance UnName VariableTerm where
  unName (VariableTerm t) = do
    maybei <- gets (L.findIndex ((==) (t ^. #id) . (^. _1)))
    case maybei of
      Just i  -> return . VariableTerm $ #id @= i <: nil
      Nothing -> do
        ctx <- get
        throwError $ #removeNamesError # RemoveNamesError (#missingVariableInNamingContext # (#name @= t ^. #id <: #namingContext @= ctx <: nil))
instance UnName AbstractionTerm where
  unName (AbstractionTerm t) = do
    ctx <- get
    let x  = t ^. #name
        ty = t ^. #type
    modify ((:) (x, VariableBind ty))
    ty' <- castEff $ evalStateDef (unName ty) ctx
    t' <- castEff $ evalStateDef (unName $ t ^. #body) ctx
    return . AbstractionTerm $ #name @= x <: #type @= ty' <: #body @= t' <: nil
instance UnName ApplicationTerm where
  unName (ApplicationTerm t) = do
    ctx <- get
    t1 <- castEff $ evalStateDef (unName $ t ^. #function) ctx
    t2 <- castEff $ evalStateDef (unName $ t ^. #argument) ctx
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil
