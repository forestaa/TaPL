{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels      #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module TaPL.SystemF where


import RIO  
import qualified RIO.Vector as V

import Control.Lens hiding ((:>), (^.))
import Control.Monad.Error.Class
-- import Control.Monad.State.Strict
import Data.Extensible
import Data.Extensible.Effect.Default

import SString


type DeBrujinIndex = Int
type NamingContext = Vector (SString, Binding)
data Binding = 
    ConstTermBind UnNamedType 
  | VariableTermBind UnNamedType 
  | ConstTypeBind 
  | VariableTypeBind 
  deriving (Show, Eq)
data NamingContextError a = 
    MissingVariableInNamingContext (Named a) NamingContext 
  | MissingTypeVariableInNamingContext (Named a) NamingContext
type UnNameError = NamingContextError 'True
type RestoreNameError = NamingContextError 'False

type family Named (a :: Bool) where
  Named 'True  = SString
  Named 'False = DeBrujinIndex
type Variable a = Record '["id" :> Named a]
-- type NamedVariable = Variable 'True
type NameLessVariable = Variable 'False


class UnName (f :: Bool -> *) where
  unName      :: f 'True -> Eff '[ReaderDef NamingContext, EitherDef UnNameError] (f 'False)
  restoreName :: f 'False -> Eff '[ReaderDef NamingContext, EitherDef RestoreNameError] (f 'True)
class IndexOperation (f :: Bool -> *) where
  indexMap :: DeBrujinIndex -> f 'False -> Eff ["onvar" >: ReaderEff (DeBrujinIndex -> NameLessVariable -> f 'False), "ontype" >: ReaderEff (DeBrujinIndex -> UnNamedType -> UnNamedType)] (f 'False)
class IndexOperation f => IndexShift (f :: Bool -> *) where
  indexShift :: DeBrujinIndex -> f 'False -> f 'False
  indexShift d = indexShift' d 0
  indexShift' :: DeBrujinIndex -> DeBrujinIndex -> f 'False -> f 'False
  -- indexShift d = leaveEff . (`runReaderDef` d) . indexShift' 0
  -- indexShift' :: DeBrujinIndex -> f 'False -> Eff '[ReaderDef DeBrujinIndex] (f 'False)
  -- indexShift' :: DeBrujinIndex -> f 'False -> f 'False
class IndexOperation f => Substitution (f :: Bool -> *) (g :: Bool -> *) where
  subst :: DeBrujinIndex -> g 'False -> f 'False -> f 'False
  -- subst j s = leaveEff . (`runReaderDef` s) . subst' j
  -- subst' :: DeBrujinIndex -> f 'False -> Eff '[ReaderDef (g 'False)] (f 'False)
betaReduction :: (IndexShift f, Substitution f f) => f 'False -> f 'False -> f 'False
betaReduction s t = indexShift (-1) $ subst 0 (indexShift 1 s) t


data Type a = 
    -- PrimitiveType SString
    VariableType (Variable a)
  | ArrowType (Record '["domain" :> Type a, "codomain" :> Type a])
  | AllType (Record '["name" :> SString, "body" :> Type a])
  | ExistType (Record '["name" :> SString, "body" :> Type a])
deriving instance (Eq (Type a), Eq (Named a)) => Eq (Type a)
instance (Show (Named a), Show (Type a)) => Show (Type a) where
  -- show (PrimitiveType ty) = show ty
  show (VariableType ty)  = show (ty ^. #id)
  show (ArrowType ty)     = concat ["(", show (ty ^. #domain), " -> ", show (ty ^. #codomain), ")"]
  show (AllType ty) = concat ["(∀", show (ty ^. #name), ".", show (ty ^. #body), ")"]
  show (ExistType ty) = concat ["(∃", show (ty ^. #name), ".", show (ty ^. #body), ")"]
type NamedType = Type 'True
type UnNamedType = Type 'False


instance UnName Type where
  -- unName (PrimitiveType ty) = return $ PrimitiveType ty
  unName (VariableType ty) =  do
    ctx <- ask
    case V.findIndex isBound ctx of
      Just i  -> return . VariableType $ #id @= i <: nil
      Nothing -> throwError $ MissingTypeVariableInNamingContext (ty ^. #id) ctx
    where
      isBound (x, VariableTypeBind) | x == ty ^. #id = True
      isBound _ = False
  unName (ArrowType ty) = do
    domain <- unName $ ty ^. #domain
    codomain <- unName $ ty ^. #codomain
    return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
  unName (AllType ty) = do
    let x  = ty ^. #name
    body <- local (V.cons (x, VariableTypeBind)) $ unName (ty ^. #body)
    return . AllType $ #name @= x <: #body @= body <: nil
  unName (ExistType ty) = do
    let x  = ty ^. #name
    body <- local (V.cons (x, VariableTypeBind)) $ unName (ty ^. #body)
    return . ExistType $ #name @= x <: #body @= body <: nil

  -- restoreName (PrimitiveType ty) = return $ PrimitiveType ty
  restoreName (VariableType ty) = do
    ctx <- ask
    case ctx V.!? (ty ^. #id) of
      Just (name, _) -> return . VariableType $ #id @= name <: nil
      Nothing        -> throwError $ MissingTypeVariableInNamingContext (ty ^. #id) ctx
  restoreName (ArrowType ty) = do
    domain <- restoreName $ ty ^. #domain
    codomain <- restoreName $ ty ^. #codomain
    return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
  restoreName (AllType ty) = do
    let x  = ty ^. #name
    body <- local (V.cons (x, VariableTypeBind)) $ restoreName (ty ^. #body)
    return . AllType $ #name @= x <: #body @= body <: nil
  restoreName (ExistType ty) = do
    let x  = ty ^. #name
    body <- local (V.cons (x, VariableTypeBind)) $ restoreName (ty ^. #body)
    return . ExistType $ #name @= x <: #body @= body <: nil
instance IndexOperation Type where
  indexMap c (VariableType ty) = asksEff #onvar (\onvar -> onvar c ty)
  indexMap c (ArrowType ty) = do
    domain <- indexMap c $ ty ^. #domain
    codomain <- indexMap c $ ty ^. #codomain
    return . ArrowType $ ty & #domain .~ domain & #codomain .~ codomain
  indexMap c (AllType ty)   = do 
    body <- indexMap (c+1) $ ty ^. #body
    return . AllType $ ty & #body .~ body
  indexMap c (ExistType ty)   = do 
    body <- indexMap (c+1) $ ty ^. #body
    return . ExistType $ ty & #body .~ body
instance IndexShift Type where
  indexShift' d c ty = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap c ty) onvar) undefined
    where
      onvar c var | var ^. #id < c = VariableType var
                  | otherwise = VariableType $ var & #id +~ d
  -- indexShift' _ _  (PrimitiveType ty) = PrimitiveType ty
  -- indexShift' c (VariableType ty) 
  --   | ty ^. #id < c = return $ VariableType ty 
  --   | otherwise =  asks $ \d -> VariableType $ ty & #id +~ d
  -- indexShift' c (ArrowType ty) = do
  --   domain <- indexShift' c $ ty ^. #domain
  --   codomain <- indexShift' c $ ty ^. #codomain
  --   return . ArrowType $ ty & #domain .~ domain & #codomain .~ codomain
  -- indexShift' c (AllType ty)   = do 
  --   body <- indexShift' (c+1) $ ty ^. #body
  --   return . AllType $ ty & #body .~ body
  -- indexShift' c (ExistType ty)   = do 
  --   body <- indexShift' (c+1) $ ty ^. #body
  --   return . ExistType $ ty & #body .~ body
instance Substitution Type Type where
  subst j s t = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap j t) onvar) undefined
    where
      onvar j var | var ^. #id == j = indexShift j s
                  | otherwise = VariableType var
  -- subst _ _ (PrimitiveType ty) = PrimitiveType ty
  -- subst' j (VariableType ty)
  --   | ty ^. #id == j = asks $ indexShift j
  --   | otherwise = return $ VariableType ty
  -- subst' j (ArrowType ty) = do
  --   domain <- subst' j $ ty ^. #domain
  --   codomain <- subst' j $ ty ^. #codomain
  --   return . ArrowType $ ty & #domain .~ domain & #codomain .~ codomain
  -- subst' j (AllType ty) = do
  --   body <- subst' (j+1) $ ty ^. #body
  --   return . AllType $ ty & #body .~ body
  -- subst' j (ExistType ty) = do
  --   body <- subst' (j+1) $ ty ^. #body
  --   return . ExistType $ ty & #body .~ body


data Term a =
    ConstTerm SString
  | VariableTerm (Variable a)
  | AbstractionTerm (Record '["name" :> SString, "type" :> Type a, "body" :> Term a])
  | ApplicationTerm (Record '["function" :> Term a, "argument" :> Term a])
  | TypeAbstractionTerm (Record '["name" :> SString, "body" :> Term a])
  | TypeApplicationTerm (Record '["body" :> Term a, "type" :> Type a])
  | PackageTerm (Record '["type" :> Type a, "term" :> Term a, "exist" :> Type a])
  | UnPackageTerm (Record '["name" :> SString, "type" :> SString, "body" :> Term a, "in" :> Term a])
deriving instance (Eq (Term a), Eq (Type a), Eq (Named a)) => Eq (Term a)
instance (Show (Named a), Show (Type a), Show (Term a)) => Show (Term a) where
  show (ConstTerm s) = show s
  show (VariableTerm t) = show (t ^. #id)
  show (AbstractionTerm t) = concat ["λ", show (t ^. #name), ":", show (t ^. #type), ".", show (t ^. #body)]
  show (ApplicationTerm t) = concat ["(", show (t ^. #function), " ", show (t ^. #argument), ")"]
  show (TypeAbstractionTerm t) = concat ["λ", show (t ^. #name), ".", show (t ^. #body)]
  show (TypeApplicationTerm t) = concat [show (t ^. #body), " [", show (t ^. #type) ,"]"]
  show (PackageTerm t) = concat ["{*", show (t ^. #type), ", ", show (t ^. #term), " as ", show (t ^. #exist)]
  show (UnPackageTerm t) = concat ["let {", show (t ^. #name), ", ", show (t ^. #type), "} = ", show (t ^. #body), " in ", show (t ^. #in)]
type NamedTerm = Term 'True
type UnNamedTerm = Term 'False

instance UnName Term where
  unName (ConstTerm s) = return $ ConstTerm s
  unName (VariableTerm t) = do
    ctx <- ask
    case V.findIndex isBound ctx of
      Just i  -> return . VariableTerm $ #id @= i <: nil
      Nothing -> throwError $ MissingVariableInNamingContext (t ^. #id) ctx
    where
      isBound (x, VariableTermBind _) | x == t ^. #id = True
      isBound _ = False
  unName (AbstractionTerm t) = do
    let x  = t ^. #name
    ty <- unName $ t ^. #type
    body <- local (V.cons (x, VariableTermBind ty)) $ unName (t ^. #body)
    return . AbstractionTerm $ #name @= x <: #type @= ty <: #body @= body <: nil
  unName (ApplicationTerm t) = do
    t1 <- unName $ t ^. #function
    t2 <- unName $ t ^. #argument
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil
  unName (TypeAbstractionTerm t) = do
    body <- local (V.cons (t ^. #name, VariableTypeBind)) $ unName (t ^. #body)
    return . TypeAbstractionTerm $ #name @= t ^. #name <: #body @= body <: nil
  unName (TypeApplicationTerm t) = do
    body <- unName $ t ^. #body
    ty   <- unName $ t ^. #type
    return . TypeApplicationTerm $ #body @= body <: #type @= ty <: nil
  unName (PackageTerm t) = do
    ty <- unName $ t ^. #type
    term <- unName $ t ^. #term
    exist <- unName $ t ^. #exist
    return . PackageTerm $ #type @= ty <: #term @= term <: #exist @= exist <: nil
  unName (UnPackageTerm t) = do
    body <- unName $ t ^. #body
    t' <- unName $ t ^. #in
    return . UnPackageTerm $ #name @= t ^. #name <: #type @= t ^. #type <: #body @= body <: #in @= t' <: nil

  restoreName (ConstTerm s) = return $ ConstTerm s
  restoreName (VariableTerm t) = do
    ctx <- ask
    case ctx V.!? (t ^. #id) of
      Just (name, _) -> return $ VariableTerm $ #id @= name <: nil
      Nothing -> throwError $ MissingVariableInNamingContext (t ^. #id) ctx
  restoreName (AbstractionTerm t) = do
    let x  = t ^. #name
        ty = t ^. #type
    ty' <- restoreName ty
    body <- local (V.cons (x, VariableTermBind ty)) $ restoreName (t ^. #body)
    return . AbstractionTerm $ #name @= x <: #type @= ty' <: #body @= body <: nil
  restoreName (ApplicationTerm t) = do
    t1 <- restoreName $ t ^. #function
    t2 <- restoreName $ t ^. #argument
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil
  restoreName (TypeAbstractionTerm t) = do
    body <- local (V.cons (t ^. #name, VariableTypeBind)) $ restoreName (t ^. #body)
    return . TypeAbstractionTerm $ #name @= t ^. #name <: #body @= body <: nil
  restoreName (TypeApplicationTerm t) = do
    body <- restoreName $ t ^. #body
    ty   <- restoreName $ t ^. #type
    return . TypeApplicationTerm $ #body @= body <: #type @= ty <: nil
  restoreName (PackageTerm t) = do
    ty <- restoreName $ t ^. #type
    term <- restoreName $ t ^. #term
    exist <- restoreName $ t ^. #exist
    return . PackageTerm $ #type @= ty <: #term @= term <: #exist @= exist <: nil
  restoreName (UnPackageTerm t) = do
    body <- restoreName $ t ^. #body
    t' <- restoreName $ t ^. #in
    return . UnPackageTerm $ #name @= t ^. #name <: #type @= t ^. #type <: #body @= body <: #in @= t' <: nil
instance IndexOperation Term where
  indexMap _ t@(ConstTerm _) = return t
  indexMap c (VariableTerm t) = asksEff #onvar (\onvar -> onvar c t)
    -- | t ^. #id < c = return $ VariableTerm t
    -- | otherwise = asks $ \d -> VariableTerm $ t & #id +~ d
  indexMap c (AbstractionTerm t) = do
    ty <- asksEff #ontype (\ontype -> ontype c $ t ^. #type)
    -- ty <- indexMap c $ t ^. #type
    body <- indexMap (c+1) $ t ^. #body
    return . AbstractionTerm $ t & #type .~ ty & #body .~ body
  indexMap c (ApplicationTerm t) = do
    f <- indexMap c $ t ^. #function
    arg <- indexMap c $ t ^. #argument
    return . ApplicationTerm $ t & #function .~ f & #argument .~ arg
  indexMap c (TypeAbstractionTerm t) = do
    body <- indexMap (c+1) $ t ^. #body
    return . TypeAbstractionTerm $ t & #body .~ body
  indexMap c (TypeApplicationTerm t) = do
    body <- indexMap c $ t ^. #body
    ty <- asksEff #ontype (\ontype -> ontype c $ t ^. #type)
    -- ty <- indexMap c $ t ^. #type
    return . TypeApplicationTerm $ t & #body .~ body & #type .~ ty
  indexMap c (PackageTerm t) = do
    -- ty <- indexShift' c $ t ^. #type
    ty <- asksEff #ontype (\ontype -> ontype c $ t ^. #type)
    term <- indexMap c $ t ^. #term
    exist <- asksEff #ontype (\ontype -> ontype c $ t ^. #exist)
    -- exist <- indexMap c $ t ^. #exist
    return . PackageTerm $ t & #type .~ ty & #term .~ term & #exist .~ exist
  indexMap c (UnPackageTerm t) = do
    body <- indexMap c $ t ^. #body
    t' <- indexMap (c+2) $ t ^. #in
    return . UnPackageTerm $ t & #body .~ body & #in .~ t'
instance IndexShift Term where
  indexShift' d c t = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap c t) onvar) ontype
    where
      onvar c var | var ^. #id < c = VariableTerm var
                  | otherwise = VariableTerm $ var & #id +~ d
      ontype = indexShift' d
  -- indexShift' _ t@(ConstTerm _) = return t
  -- indexShift' c (VariableTerm t)
  --   | t ^. #id < c = return $ VariableTerm t
  --   | otherwise = asks $ \d -> VariableTerm $ t & #id +~ d
  -- indexShift' c (AbstractionTerm t) = do
  --   ty <- indexShift' c $ t ^. #type
  --   body <- indexShift' (c+1) $ t ^. #body
  --   return . AbstractionTerm $ t & #type .~ ty & #body .~ body
  -- indexShift' c (ApplicationTerm t) = do
  --   f <- indexShift' c $ t ^. #function
  --   arg <- indexShift' c $ t ^. #argument
  --   return . ApplicationTerm $ t & #function .~ f & #argument .~ arg
  -- indexShift' c (TypeAbstractionTerm t) = do
  --   body <- indexShift' (c+1) $ t ^. #body
  --   return . TypeAbstractionTerm $ t & #body .~ body
  -- indexShift' c (TypeApplicationTerm t) = do
  --   body <- indexShift' c $ t ^. #body
  --   ty <- indexShift' c $ t ^. #type
  --   return . TypeApplicationTerm $ t & #body .~ body & #type .~ ty
  -- indexShift' c (PackageTerm t) = do
  --   ty <- indexShift' c $ t ^. #type
  --   term <- indexShift' c $ t ^. #term
  --   exist <- indexShift' c $ t ^. #exist
  --   return . PackageTerm $ t & #type .~ ty & #term .~ term & #exist .~ exist
  -- indexShift' c (UnPackageTerm t) = do
  --   body <- indexShift' c $ t ^. #body
  --   t' <- indexShift' (c+2) $ t ^. #in
  --   return . UnPackageTerm $ t & #body .~ body & #in .~ t'
instance Substitution Term Term where
  subst j s t = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap j t) onvar) ontype
    where
      onvar j var | var ^. #id == j = indexShift j s
                  | otherwise = VariableTerm var
      ontype _ ty = ty
  -- subst' _ t@(ConstTerm _) = return t
  -- subst' j (VariableTerm t)
  --   | t ^. #id == j = asks $ indexShift j
  --   | otherwise = return $ VariableTerm t
  -- subst' j (AbstractionTerm t) = do
  --   body <- subst' (j+1) $ t ^. #body
  --   return . AbstractionTerm $ t & #body .~ body
  -- subst' j (ApplicationTerm t) = do
  --   f <- subst' j $ t ^. #function
  --   arg <- subst' j $ t ^. #argument
  --   return . ApplicationTerm $ t & #function .~ f & #argument .~ arg
  -- subst' j (TypeAbstractionTerm t) = do
  --   body <- subst' (j+1) $ t ^. #body
  --   return . TypeAbstractionTerm $ t & #body .~ body
  -- subst' j (TypeApplicationTerm t) = do
  --   body <- subst' j $ t ^. #body
  --   return . TypeApplicationTerm $ t & #body .~ body
  -- subst' j (PackageTerm t) = do
  --   term <- subst' j $ t ^. #term
  --   return . PackageTerm $ t & #term .~ term
  -- subst' j (UnPackageTerm t) = do
  --   body <- subst' j $ t ^. #body
  --   t' <- subst' (j+2) $ t ^. #in
  --   return . UnPackageTerm $ t & #body .~ body & #in .~ t'

instance Substitution Term Type where
  subst j s t = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap j t) onvar) ontype
    where
      onvar _ var = VariableTerm var
      ontype j ty = subst j s ty