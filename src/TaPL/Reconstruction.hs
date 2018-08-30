{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE OverloadedLabels   #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE PolyKinds #-}

module TaPL.Reconstruction where


import RIO
import qualified RIO.Map as Map
import qualified RIO.Set as Set
import qualified RIO.Vector as V

import Control.Monad.State.Strict
import Control.Monad.Error.Class

import Data.Extensible
import Data.Extensible.Effect.Default

import SString


type DeBrujinIndex = Int

type NamedTerm = Term 'True
type UnNamedTerm = Term 'False

type family Named (a :: Bool) where
  Named 'True  = SString
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


mapEitherDef :: (e -> e') -> Eff '[EitherDef e] a -> Eff '[EitherDef e'] a 
mapEitherDef f m = do
  ret <- castEff $ runEitherDef m
  case ret of
    Right a -> return a
    Left e -> throwError $ f e

data Type = 
    -- PrimitiveType SString
    NatType
  | BoolType
  | VariableType VariableType
  | ArrowType (Record '["domain" >: Type, "codomain" >: Type])
  | PairType Type Type
  | TypeScheme (Record '["schemes" >: Set.Set VariableType, "type" >: Type])
  deriving (Eq, Ord)
-- type VariableType = Int
type VariableType = SString
data Term a = 
    Zero
  | Succ (Term a)
  | Pred (Term a)
  | IsZero (Term a)
  | TRUE
  | FALSE
  | If (Record '["cond" :> Term a, "then" :> Term a, "else" :> Term a])
  | VariableTerm (Named a)
  | AbstractionTerm (Record '["name" :> SString, "type" :> Type, "body" :> Term a])
  | ApplicationTerm (Record '["function" :> Term a, "argument" :> Term a])
  | FixTerm (Term a)
  | PairTerm (Term a) (Term a)
  | ImplicitAbstractionTerm (Record '["name" :> SString, "body" :> Term a])
  | LetTerm (Record '["name" >: SString, "body" :> Term a, "in" :> Term a])
data Binding = 
    ConstTermBind Type
  | VariableTermBind Type
  | ImplicitVariableTermBind
  | ConstTypeBind 
  | VariableTypeBind 
  deriving (Show, Eq)
type NamingContext = Vector (SString, Binding)
type Constraints = Set.Set (Type, Type)
type Unifier = Map.Map VariableType Type

data Errors = 
    UnNameError UnNameError
  | TypingError TypingError
  | RestoreNameError RestoreNameError
  deriving (Eq)
data NamingContextError a = 
    MissingVariableInNamingContext (Named a) NamingContext 
  | MissingTypeVariableInNamingContext (Named a) NamingContext
type UnNameError = NamingContextError 'True
type RestoreNameError = NamingContextError 'False
data TypingError = ReconstructionError ReconstructionError deriving (Eq)
data ReconstructionError = 
    MissingVariableTypeInNamingContext  DeBrujinIndex NamingContext 
  | UnifyError UnifyError
  deriving (Eq)
data UnifyError = 
    Conflict
  | InstantiateFalied 
  deriving (Show, Eq)


deriving instance Eq (Named a) => Eq (Term a)
deriving instance Eq (Named a) => Eq (NamingContextError a)
instance Show Type where
  -- show (PrimitiveType ty) = show ty
  show NatType = "Nat"
  show BoolType = "Bool"
  -- show (VariableType n)  = "?X_" ++ show n
  show (VariableType name) = show name
  show (ArrowType ty)     = concat ["(", show (ty ^. #domain), " -> ", show (ty ^. #codomain), ")"]
  show (PairType ty1 ty2) = concat ["(", show ty1, ", ", show ty2, ")"]
  show (TypeScheme ty) = concat ["∀", foldMap show (ty ^. #schemes), ".", show (ty ^. #type)]

instance (Show (Named a)) => Show (Term a) where
  show Zero = "z"
  show (Succ t) = concat ["s(", show t, ")"]
  show (Pred t) = concat ["pred(", show t, ")"]
  show (IsZero t) = concat ["iszero ", show t]
  show TRUE = "True"
  show FALSE = "False"
  show (If t) = concat ["if ", show (t ^. #cond), " then ", show (t ^. #then), " else ", show (t ^. #else)]
  show (VariableTerm name) = show name
  show (AbstractionTerm t) = concat ["λ", show (t ^. #name), ":", show (t ^. #type), ".", show (t ^. #body)]
  show (ApplicationTerm t) = concat ["(", show (t ^. #function), " ", show (t ^. #argument), ")"]
  show (FixTerm t) = concat ["fix ", show t]
  show (PairTerm t1 t2) = concat ["(", show t1, ", ", show t2, ")"]
  show (ImplicitAbstractionTerm t) = concat ["λ", show (t ^. #name), ".", show (t ^. #body)]
  show (LetTerm t) = concat ["let ", show (t ^. #name), " = ", show (t ^. #body), " in ", show (t ^. #in)]


instance Show Errors where
  show (UnNameError e) = "UnName Error: " ++ show e
  show (TypingError e) = "Typing Error: " ++ show e
  show (RestoreNameError e) = "RestoreName Error: " ++ show e
instance Show (Named a) => Show (NamingContextError a) where
  show (MissingVariableInNamingContext name ctx) = concat ["missing variable in naming context: variable: ", show name, ", NamingContext: ", show ctx]
  show (MissingTypeVariableInNamingContext name ctx) = concat ["missing type variable in naming context: type variable: ", show name, ", NamingContext: ", show ctx]
instance Show TypingError where
  show (ReconstructionError e) = "Reconstruction Error: " ++ show e
instance Show ReconstructionError where
  show (MissingVariableTypeInNamingContext name ctx) = concat ["missing variable in naming context: variable: ", show name, ", NamingContext: ", show ctx]
  show (UnifyError e) = "Unify Error: " ++ show e
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
      Just i  -> return $ VariableTerm i
      Nothing -> do
        ctx <- getEff #context
        throwError $ MissingVariableInNamingContext t ctx
    where
      isBound (x, VariableTermBind _) | x == t = True
      isBound (x, ImplicitVariableTermBind) | x == t = True
      isBound _ = False
  unName (AbstractionTerm t) = do
    let x  = t ^. #name
        ty = t ^. #type
    modifyEff #context (V.cons (x, VariableTermBind ty))
    body <- unName $ t ^. #body
    return . AbstractionTerm $ #name @= x <: #type @= ty <: #body @= body <: nil
  unName (ApplicationTerm t) = do
    ctx <- getEff #context
    t1 <- castEff $ evalStateEff @"context" (unName $ t ^. #function) ctx
    t2 <- castEff $ evalStateEff @"context" (unName $ t ^. #argument) ctx
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil
  unName (FixTerm t) = FixTerm <$> unName t
  unName (PairTerm t1 t2) = do
    ctx <- getEff #context
    t1' <- castEff $ evalStateEff @"context" (unName t1) ctx
    t2' <- castEff $ evalStateEff @"context" (unName t2) ctx
    return $ PairTerm t1' t2'
  unName (ImplicitAbstractionTerm t) = do
    let x = t ^. #name
    modifyEff #context (V.cons (x, ImplicitVariableTermBind))
    body <- unName $ t ^. #body
    return . ImplicitAbstractionTerm $ #name @= x <: #body @= body <: nil
  unName (LetTerm t) = do
    let x = t ^. #name
    ctx <- modifyEff #context (V.cons (x, ImplicitVariableTermBind)) >> getEff #context
    body <- castEff $ evalStateEff @"context" (unName $ t ^. #body) ctx
    t' <- unName $ t ^. #in
    return . LetTerm $ #name @= x <: #body @= body <: #in @= t' <: nil


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
    case ctx V.!? t of
      Just (name, _) -> return $ VariableTerm name
      Nothing -> getEff #context >>= throwError . MissingVariableInNamingContext t
  restoreName (AbstractionTerm t) = do
    let x  = t ^. #name
        ty = t ^. #type
    modifyEff #context (V.cons (x, VariableTermBind ty))
    t'  <- restoreName $ t ^. #body
    return . AbstractionTerm $ #name @= x <: #type @= ty <: #body @= t' <: nil
  restoreName (ApplicationTerm t) = do
    ctx <- getEff #context
    t1 <- castEff $ evalStateEff @"context" (restoreName $ t ^. #function) ctx
    t2 <- castEff $ evalStateEff @"context" (restoreName $ t ^. #argument) ctx
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil
  restoreName (FixTerm t) = FixTerm <$> restoreName t
  restoreName (PairTerm t1 t2) = do
    ctx <- getEff #context
    t1' <- castEff $ evalStateEff @"context" (restoreName t1) ctx
    t2' <- castEff $ evalStateEff @"context" (restoreName t2) ctx
    return $ PairTerm t1' t2'
  restoreName (ImplicitAbstractionTerm t) = do
    let x = t ^. #name
    modifyEff #context (V.cons (x, ImplicitVariableTermBind))
    body <- restoreName $ t ^. #body
    return . ImplicitAbstractionTerm $ #name @= x <: #body @= body <: nil
  restoreName (LetTerm t) = do
    let x = t ^. #name
    ctx <- modifyEff #context (V.cons (x, ImplicitVariableTermBind)) >> getEff #context
    body <- castEff $ evalStateEff @"context" (restoreName $ t ^. #body) ctx
    t' <- restoreName $ t ^. #in
    return . LetTerm $ #name @= x <: #body @= body <: #in @= t' <: nil

leaveUnName :: NamingContext -> NamedTerm -> Either UnNameError UnNamedTerm
leaveUnName ctx t = leaveEff . runEitherDef $ evalStateEff @"context" (unName t) ctx
leaveRestoreName :: NamingContext -> UnNamedTerm -> Either RestoreNameError NamedTerm
leaveRestoreName ctx t = leaveEff . runEitherDef $ evalStateEff @"context" (restoreName t) ctx

freshTypeVariable :: Associate "fresh" (State Int) xs => Eff xs VariableType
freshTypeVariable = do
  n <- getEff #fresh
  putEff #fresh (n+1)
  return . pack $ "?X_" ++ show n

reconstruction :: UnNamedTerm -> Eff '["context" >: State NamingContext,  "fresh" >: State Int, EitherDef ReconstructionError] (Type, Unifier)
reconstruction Zero = return (NatType, Map.empty)
reconstruction (Succ t) = do
  (ty, unifier1) <- reconstruction t
  unifier2 <- castEff . mapEitherDef UnifyError . unify $ Set.singleton (ty, NatType)
  unifier <- castEff . mapEitherDef UnifyError $ union unifier1 unifier2
  return (NatType, unifier)
reconstruction (Pred t) = do
  (ty, unifier1) <- reconstruction t
  unifier2 <- castEff . mapEitherDef UnifyError . unify $ Set.singleton (ty, NatType)
  unifier <- castEff . mapEitherDef UnifyError $ union unifier1 unifier2
  return (NatType, unifier)
reconstruction (IsZero t) = do
  (ty, unifier1) <- reconstruction t
  unifier2 <- castEff . mapEitherDef UnifyError . unify $ Set.singleton (ty, NatType)
  unifier <- castEff . mapEitherDef UnifyError $ union unifier1 unifier2
  return (BoolType, unifier)
reconstruction TRUE = return (BoolType, Map.empty)
reconstruction FALSE = return (BoolType, Map.empty)
reconstruction (If t) = do
  ctx <- getEff #context
  (ty1, unifier1) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #cond) ctx
  (ty2, unifier2) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #then) ctx
  (ty3, unifier3) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #else) ctx
  unifier4 <- castEff . mapEitherDef UnifyError . unify $ Set.fromList [(ty1, BoolType), (ty2, ty3)]
  unifier <- castEff . mapEitherDef UnifyError $ unions [unifier1, unifier2, unifier3, unifier4]
  let ty = leaveEff $ runReaderDef (instantiate ty2) unifier
  return (ty, unifier)
reconstruction (VariableTerm t) = do
  ctx <- getEff #context
  case ctx V.!? t of
    Just (_, VariableTermBind ty) -> return (ty, Map.empty)
    _ -> throwError $ MissingVariableTypeInNamingContext t ctx
reconstruction (AbstractionTerm t) = do
  modifyEff #context $ V.cons (t ^. #name, VariableTermBind $ t ^. #type)
  (bodyty, unifier) <- reconstruction $ t ^. #body
  let ty = leaveEff $ runReaderDef (instantiate (t ^. #type)) unifier
  return (ArrowType $ #domain @= ty <: #codomain @= bodyty <: nil, unifier)
reconstruction (ApplicationTerm t)  = do
  ctx <- getEff #context
  (ty1, unifier1) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #function) ctx
  (ty2, unifier2) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #argument) ctx
  typevar <- VariableType <$> freshTypeVariable
  unifier3 <- castEff . mapEitherDef UnifyError . unify $ Set.singleton (ty1, ArrowType $ #domain @= ty2 <: #codomain @= typevar <: nil)
  unifier <- castEff . mapEitherDef UnifyError $ unions [unifier1, unifier2, unifier3]
  let ty = leaveEff $ runReaderDef (instantiate typevar) unifier
  return (ty, unifier)
reconstruction (FixTerm f) = do
  (ty, unifier1) <- reconstruction f
  typevar <- VariableType <$> freshTypeVariable
  unifier2 <- castEff . mapEitherDef UnifyError . unify $ Set.singleton (ty, ArrowType $ #domain @= typevar <: #codomain @= typevar <: nil)
  unifier <- castEff . mapEitherDef UnifyError $ union unifier1 unifier2
  let ty = leaveEff $ runReaderDef (instantiate typevar) unifier
  return (ty, unifier)

leaveReconstruction :: NamingContext -> UnNamedTerm -> Either ReconstructionError Type
leaveReconstruction ctx t = fmap fst . leaveEff . runEitherDef $ evalStateEff @"fresh" (evalStateEff @"context" (reconstruction t) ctx) 0

-- ty == ty' is not sufficient, for example, VariableType n != NatType but we should refine it
insert :: VariableType -> Type -> Unifier -> Eff '[EitherDef UnifyError] Unifier
insert n ty unifier = case unifier Map.!? n of
  Just ty' -> if ty == ty' then return unifier else throwError Conflict
  Nothing -> return $ Map.insert n ty unifier

union :: Unifier -> Unifier -> Eff '[EitherDef UnifyError] Unifier
union u1 = Map.foldrWithKey (\v ty -> (=<<) (insert v ty)) (return u1)

unions :: [Unifier] -> Eff '[EitherDef UnifyError] Unifier
unions = foldr ((=<<) . union) (return Map.empty)

unify :: Constraints -> Eff '[EitherDef UnifyError] Unifier
unify c = case Set.lookupMin c of
  Nothing -> return Map.empty
  Just (s, t) | s == t  -> unify $ Set.deleteMin c
  Just (v@(VariableType n), t) | not (occurCheck v t) -> unify (Set.deleteMin c) >>= insert n t
  Just (s, v@(VariableType n)) | not (occurCheck v s) -> unify (Set.deleteMin c) >>= insert n s
  Just (ArrowType ty1, ArrowType ty2) -> unify . Set.insert (ty1 ^. #domain, ty2 ^. #domain) . Set.insert (ty1 ^. #codomain, ty2 ^. #codomain) $ Set.deleteMin c
  _ -> throwError Conflict
  where
    occurCheck v t@(VariableType _) = v == t
    occurCheck v (ArrowType ty) = occurCheck v (ty ^. #domain) || occurCheck v (ty ^. #codomain)
    occurCheck _ _ = False

-- TODO: infinite loop risk, x = y = z
refineUnifer :: Unifier -> Eff '[EitherDef UnifyError] Unifier
refineUnifer sigma = traverse (castEff . flip runReaderDef sigma . instantiate) sigma

instantiate :: Type -> Eff '[ReaderDef Unifier] Type
instantiate (VariableType name) = do
  sigma <- ask
  case sigma Map.!? name of
    Just ty -> instantiate ty
    Nothing -> return $ VariableType name
instantiate (ArrowType ty') = do
  domain <- instantiate $ ty' ^. #domain
  codomain <- instantiate $ ty' ^. #codomain
  return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
instantiate t = return t

unify' :: Constraints -> Eff '[EitherDef UnifyError] Unifier
unify' = unify >=> refineUnifer

typeOf :: NamingContext -> UnNamedTerm -> Eff '[EitherDef TypingError] Type
typeOf ctx t = fmap fst . mapEitherDef  ReconstructionError $ evalStateEff @"fresh"   (evalStateEff @"context" (reconstruction t) ctx) 0
  -- sigma <- mapEitherDef UnifyError $ unify' c
  -- castEff $ runReaderDef (instantiate ty) sigma

