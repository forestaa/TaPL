{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE OverloadedLabels   #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE UndecidableInstances #-}

module TaPL.Reconstruction where


import RIO
import qualified RIO.Set as Set
import qualified RIO.Vector as V

import Control.Monad.State.Strict
import Control.Monad.Error.Class

import Data.Extensible
import Data.Extensible.Effect.Default

import qualified SString


type DeBrujinIndex = Int

type NamedTerm = Term 'True
type UnNamedTerm = Term 'False

type family Named (a :: Bool) where
  Named 'True  = SString.SString
  Named 'False = DeBrujinIndex

class UnName (f :: Bool -> *) where
  unName      :: f 'True -> Eff '["context" >: State NamingContext, EitherDef UnNameError] (f 'False)
  restoreName :: f 'False -> Eff '["context" >: State NamingContext, EitherDef RestoreNameError] (f 'True)
class IndexShift (f :: Bool -> *) where
  indexShift :: DeBrujinIndex -> f 'False -> f 'False
class Substitution (f :: Bool -> *) where
  subst :: DeBrujinIndex -> f 'False -> f 'False -> f 'False
betaReduction :: (IndexShift f, Substitution f) => f 'False -> f 'False -> f 'False
betaReduction s t = indexShift (-1) $ subst 0 (indexShift 1 s) t


data Type = 
    NatType
  | BoolType
  | VariableType (Record '["id" :> SString.SString])
  | ArrowType (Record '[ "domain" >: Type, "codomain" >: Type])
  deriving (Eq, Ord)
-- deriving instance (Eq (Named a)) => Eq (Type a)
-- deriving instance (Ord (Named a)) => Ord (Type a)
data Term a = 
    Zero
  | Succ (Term a)
  | Pred (Term a)
  | IsZero (Term a)
  | TRUE
  | FALSE
  | If (Record '["cond" :> Term a, "then" :> Term a, "else" :> Term a])
  | VariableTerm (Record '["id" :> Named a])
  | AbstractionTerm (Record '["name" :> SString.SString, "type" :> Type, "body" :> Term a])
  | ApplicationTerm (Record '["function" :> Term a, "argument" :> Term a])
data Binding = 
    ConstTermBind Type
  | VariableTermBind Type
  | ConstTypeBind 
  | VariableTypeBind 
  -- deriving (Show, Eq)
type NamingContext = Vector (SString.SString, Binding)
type Constraints = Set.Set (Type, Type)

data NamingContextError a = 
    MissingVariableInNamingContext (Named a) NamingContext 
  | MissingTypeVariableInNamingContext (Named a) NamingContext
type UnNameError = NamingContextError 'True
type RestoreNameError = NamingContextError 'False
data ReconstructionError = MissingVariableTypeInNamingContext  DeBrujinIndex NamingContext


-- instance UnName Type where
--   unName NatType = return NatType
--   unName BoolType = return BoolType
--   unName (VariableType ty) =  do
--     maybei <- V.findIndex isBound <$> getEff #context
--     case maybei of
--       Just i  -> return . VariableType $ #id @= i <: nil
--       Nothing -> do
--         ctx <- getEff #context
--         throwError $ MissingTypeVariableInNamingContext (ty ^. #id) ctx
--     where
--       isBound (x, VariableTypeBind) | x == ty ^. #id = True
--       isBound _ = False
--   unName (ArrowType ty) = do
--     domain <- unName $ ty ^. #domain
--     codomain <- unName $ ty ^. #codomain
--     return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil

--   restoreName NatType = return NatType
--   restoreName BoolType = return BoolType
--   restoreName (VariableType ty) = do
--     ctx <- getEff #context
--     case ctx V.!? (ty ^. #id) of
--       Just (name, _) -> return . VariableType $ #id @= name <: nil
--       Nothing        -> throwError $ MissingTypeVariableInNamingContext (ty ^. #id) ctx
--   restoreName (ArrowType ty) = do
--     domain <- restoreName $ ty ^. #domain
--     codomain <- restoreName $ ty ^. #codomain
--     return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
 
instance UnName Term where
  unName Zero = return Zero
  unName (Succ t) = Succ <$> unName t
  unName (Pred t) = Pred <$> unName t
  unName (IsZero t) = IsZero <$> unName t
  unName TRUE = return TRUE
  unName FALSE = return FALSE
  unName (If t) = do
    ctx <- getEff #context
    t1 <- castEff $ evalStateEff @"context" (unName $ t ^. #cond) ctx
    t2 <- castEff $ evalStateEff @"context" (unName $ t ^. #then) ctx
    t3 <- castEff $ evalStateEff @"context" (unName $ t ^. #else) ctx
    return . If $ #cond @= t1 <: #then @= t2 <: #else @= t3 <: nil
  unName (VariableTerm t) = do
    maybei <- V.findIndex isBound <$> getEff #context
    case maybei of
      Just i  -> return . VariableTerm $ #id @= i <: nil
      Nothing -> do
        ctx <- getEff #context
        throwError $ MissingVariableInNamingContext (t ^. #id) ctx
    where
      isBound (x, VariableTermBind _) | x == t ^. #id = True
      isBound _ = False
  unName (AbstractionTerm t) = do
    let x  = t ^. #name
        ty = t ^. #type
    newctx <- modifyEff #context (V.cons (x, VariableTermBind ty)) >> getEff #context
    t' <- castEff $ evalStateEff @"context" (unName $ t ^. #body) newctx
    return . AbstractionTerm $ #name @= x <: #type @= ty <: #body @= t' <: nil
  unName (ApplicationTerm t) = do
    ctx <- getEff #context
    t1 <- castEff $ evalStateEff @"context" (unName $ t ^. #function) ctx
    t2 <- castEff $ evalStateEff @"context" (unName $ t ^. #argument) ctx
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil


  restoreName Zero = return Zero
  restoreName (Succ t) = Succ <$> restoreName t
  restoreName (Pred t) = Pred <$> restoreName t
  restoreName (IsZero t) = IsZero <$> restoreName t
  restoreName TRUE = return TRUE
  restoreName FALSE = return FALSE
  restoreName (If t) = do
    ctx <- getEff #context
    t1 <- castEff $ evalStateEff @"context" (restoreName $ t ^. #cond) ctx
    t2 <- castEff $ evalStateEff @"context" (restoreName $ t ^. #then) ctx
    t3 <- castEff $ evalStateEff @"context" (restoreName $ t ^. #else) ctx
    return . If $ #cond @= t1 <: #then @= t2 <: #else @= t3 <: nil
  restoreName (VariableTerm t) = do
    ctx <- getEff #context
    case ctx V.!? (t ^. #id) of
      Just (name, _) -> return $ VariableTerm $ #id @= name <: nil
      Nothing -> getEff #context >>= throwError . MissingVariableInNamingContext (t ^. #id)
  restoreName (AbstractionTerm t) = do
    let x  = t ^. #name
        ty = t ^. #type
    newctx <- modifyEff #context (V.cons (x, VariableTermBind ty)) >> getEff #context
    t'  <- castEff $ evalStateEff @"context" (restoreName $ t ^. #body) newctx
    return . AbstractionTerm $ #name @= x <: #type @= ty <: #body @= t' <: nil
  restoreName (ApplicationTerm t) = do
    ctx <- getEff #context
    t1 <- castEff $ evalStateEff @"context" (restoreName $ t ^. #function) ctx
    t2 <- castEff $ evalStateEff @"context" (restoreName $ t ^. #argument) ctx
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil




freshTypeVariable :: Associate "fresh" (State Int) xs => Eff xs SString.SString
freshTypeVariable = do
  n <- getEff #fresh
  modifyEff #fresh (+ 1)
  return $ "?X_" <> SString.pack (show n)

reconstruction :: UnNamedTerm -> Eff '["context" >: State NamingContext,  "fresh" >: State Int, EitherDef ReconstructionError] (Type, Constraints)
reconstruction Zero = return (NatType, Set.empty)
reconstruction (Succ t) = do
  (ty, c) <- reconstruction t
  return (NatType, Set.insert (ty, NatType) c)
reconstruction (Pred t) = do
  (ty, c) <- reconstruction t
  return (NatType, Set.insert (ty, NatType) c)
reconstruction (IsZero t) = do
  (ty, c) <- reconstruction t
  return (BoolType, Set.insert (ty, NatType) c)
reconstruction TRUE = return (BoolType, Set.empty)
reconstruction FALSE = return (BoolType, Set.empty)
reconstruction (If t) = do
  ctx <- getEff #context
  (ty1, c1) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #cond) ctx
  (ty2, c2) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #then) ctx
  (ty3, c3) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #else) ctx
  return (ty2, (ty1, BoolType) `Set.insert` ((ty2, ty3) `Set.insert` (c1 `Set.union` c2 `Set.union` c3)))
reconstruction (VariableTerm t) = do
  ctx <- getEff #context
  case ctx V.!? (t ^. #id) of
    Just (_, VariableTermBind ty) -> return (ty, Set.empty)
    _ -> throwError $ MissingVariableTypeInNamingContext (t ^. #id) ctx
reconstruction (AbstractionTerm t) = do
  modifyEff #context $ V.cons (t ^. #name, VariableTermBind $ t ^. #type)
  (bodyty, c) <- reconstruction $ t ^. #body
  return (ArrowType $ #domain @= t ^. #type <: #codomain @= bodyty <: nil, c)
reconstruction (ApplicationTerm t)  = do
  ctx <- getEff #context
  (ty1, c1) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #function) ctx
  (ty2, c2)<- castEff $ evalStateEff @"context" (reconstruction $ t ^. #argument) ctx
  typevar <- VariableType . (\id -> #id @= id <: nil) <$> freshTypeVariable
  return (typevar, c1 `Set.union` c2 `Set.union` Set.singleton (ty1, ArrowType $ #domain @= ty2 <: #codomain @= typevar <: nil))