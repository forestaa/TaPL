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

import qualified Debug.Trace as D


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
  | UnifyError NamingContext UnNamedTerm UnifyError
  deriving (Eq)
data UnifyError = 
    ConstraintsConflict Constraints
  | UnifierInsertConflict VariableType Type Unifier
  deriving (Eq)


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
  show (UnifyError ctx t e) = concat ["NamingContext = ", show ctx, ", Term = ", show t, ": Unify Error: ", show e]
instance Show UnifyError where
  show (ConstraintsConflict c) = concat ["failed to resolve conflicts: constraints", show c]
  show (UnifierInsertConflict n ty unifier) = concat ["conflict unifier: TypeVariable = ", show n, ", Type = ", show ty, ", Unifier = ", show unifier]

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
    ctx <- getEff #context
    body <- castEff $ evalStateEff @"context" (unName $ t ^. #body) ctx
    modifyEff #context (V.cons (x, ImplicitVariableTermBind))
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
    ctx <- getEff #context
    body <- castEff $ evalStateEff @"context" (restoreName $ t ^. #body) ctx
    modifyEff #context (V.cons (x, ImplicitVariableTermBind))
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
  ctx <- getEff #context
  unifier2 <- castEff . mapEitherDef (UnifyError ctx (Succ t)) . unify $ Set.singleton (ty, NatType)
  unifier <- castEff . mapEitherDef (UnifyError ctx (Succ t)) $ union unifier1 unifier2
  return (NatType, unifier)
reconstruction (Pred t) = do
  (ty, unifier1) <- reconstruction t
  ctx <- getEff #context
  unifier2 <- castEff . mapEitherDef (UnifyError ctx (Pred t)). unify $ Set.singleton (ty, NatType)
  unifier <- castEff . mapEitherDef (UnifyError ctx (Pred t)) $ union unifier1 unifier2
  return (NatType, unifier)
reconstruction (IsZero t) = do
  (ty, unifier1) <- reconstruction t
  ctx <- getEff #context
  unifier2 <- castEff . mapEitherDef (UnifyError ctx (IsZero t)) . unify $ Set.singleton (ty, NatType)
  unifier <- castEff . mapEitherDef (UnifyError ctx (IsZero t)) $ union unifier1 unifier2
  return (BoolType, unifier)
reconstruction TRUE = return (BoolType, Map.empty)
reconstruction FALSE = return (BoolType, Map.empty)
reconstruction (If t) = do
  ctx <- getEff #context
  (ty1, unifier1) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #cond) ctx
  (ty2, unifier2) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #then) ctx
  (ty3, unifier3) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #else) ctx
  unifier4 <- castEff . mapEitherDef (UnifyError ctx (If t)). unify $ Set.fromList [(ty1, BoolType), (ty2, ty3)]
  unifier <- castEff . mapEitherDef (UnifyError ctx (If t)) $ unions [unifier1, unifier2, unifier3, unifier4]
  return (instantiate unifier ty2, unifier)
reconstruction (VariableTerm t) = do
  ctx <- getEff #context
  case ctx V.!? t of
    Just (_, VariableTermBind (TypeScheme ty)) -> do
      unifier <- foldM (\m v -> freshTypeVariable >>= \newv -> return $ Map.insert v (VariableType newv) m) Map.empty (ty ^. #schemes)
      return (instantiate unifier (ty ^. #type), Map.empty)
    Just (_, VariableTermBind ty) -> return (ty, Map.empty)
    _ -> throwError $ MissingVariableTypeInNamingContext t ctx
reconstruction (AbstractionTerm t) = do
  modifyEff #context $ V.cons (t ^. #name, VariableTermBind $ t ^. #type)
  (bodyty, unifier) <- reconstruction $ t ^. #body
  let ty = ArrowType $ #domain @= instantiate unifier (t ^. #type) <: #codomain @= bodyty <: nil
  return (ty, unifier)
reconstruction (ApplicationTerm t)  = do
  ctx <- getEff #context
  (ty1, unifier1) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #function) ctx
  (ty2, unifier2) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #argument) ctx
  typevar <- VariableType <$> freshTypeVariable
  unifier3 <- castEff . mapEitherDef (UnifyError ctx (ApplicationTerm t)) . unify $ Set.singleton (ty1, ArrowType $ #domain @= ty2 <: #codomain @= typevar <: nil)
  unifier <- castEff . mapEitherDef (UnifyError ctx (ApplicationTerm t)) $ unions [unifier1, unifier2, unifier3]
  return (instantiate unifier typevar, unifier)
reconstruction (FixTerm f) = do
  (ty, unifier1) <- reconstruction f
  typevar <- VariableType <$> freshTypeVariable
  ctx <- getEff #context
  unifier2 <- castEff . mapEitherDef (UnifyError ctx (FixTerm f)) . unify $ Set.singleton (ty, ArrowType $ #domain @= typevar <: #codomain @= typevar <: nil)
  unifier <- castEff . mapEitherDef (UnifyError ctx (FixTerm f)) $ union unifier1 unifier2
  return (instantiate unifier typevar, unifier)
reconstruction (PairTerm t1 t2) = do
  ctx <- getEff #context
  (ty1, unifier1) <- castEff $ evalStateEff @"context" (reconstruction t1) ctx
  (ty2, unifier2) <- castEff $ evalStateEff @"context" (reconstruction t2) ctx
  unifier <- castEff . mapEitherDef (UnifyError ctx (PairTerm t1 t2)) $ union unifier1 unifier2
  return (instantiate unifier (PairType ty1 ty2), unifier)
reconstruction (ImplicitAbstractionTerm t) = do
  typevar <- VariableType <$> freshTypeVariable
  modifyEff #context $ V.cons (t ^. #name, VariableTermBind typevar)
  (bodyty, unifier) <- reconstruction $ t ^. #body
  let ty = ArrowType $ #domain @= instantiate unifier typevar <: #codomain @= bodyty <: nil
  return (ty, unifier)
reconstruction (LetTerm t) = do
  ctx <- getEff #context
  (ty1, unifier1) <- castEff $ evalStateEff @"context" (reconstruction $ t ^. #body) ctx
  let typevariables = leaveEff $ runReaderDef (freeVariable ty1) (extractVariableTypeFromNamingContext ctx)
  modifyEff #context $ V.cons (t ^. #name, VariableTermBind $ TypeScheme (#schemes @= typevariables <: #type @= ty1 <: nil))
  (ty2, unifier2) <- reconstruction $ t ^. #in
  ctx' <- getEff #context
  unifier <- castEff . mapEitherDef (UnifyError ctx' (LetTerm t)) $ union unifier1 unifier2
  return (ty2, unifier)

extractVariableType :: Type -> Set.Set VariableType
extractVariableType (VariableType n) = Set.singleton n
extractVariableType (ArrowType ty) = extractVariableType (ty ^. #domain) `Set.union` extractVariableType (ty ^. #codomain)
extractVariableType (PairType ty1 ty2) = extractVariableType ty1 `Set.union` extractVariableType ty2
extractVariableType _ = Set.empty

extractVariableTypeFromNamingContext :: NamingContext -> Set.Set VariableType
extractVariableTypeFromNamingContext = foldr f Set.empty
  where
    f (_, VariableTermBind ty) = Set.union (extractVariableType ty)
    f _ = id

freeVariable :: Type -> Eff '[ReaderDef (Set.Set VariableType) ] (Set.Set VariableType)
freeVariable (VariableType n) = asks (bool (Set.singleton n) Set.empty . Set.member n)
freeVariable (ArrowType ty) = Set.union <$> freeVariable (ty ^. #domain) <*> freeVariable (ty ^. #codomain)
freeVariable (PairType ty1 ty2) = Set.union <$> freeVariable ty1 <*> freeVariable ty2
freeVariable _ = return Set.empty


leaveReconstruction :: NamingContext -> UnNamedTerm -> Either ReconstructionError Type
leaveReconstruction ctx t = fmap fst . leaveEff . runEitherDef $ evalStateEff @"fresh" (evalStateEff @"context" (reconstruction t) ctx) 0

-- ty == ty' is not sufficient, for example, VariableType n != NatType but we should refine it
insert :: VariableType -> Type -> Unifier -> Eff '[EitherDef UnifyError] Unifier
insert n ty unifier = case unifier Map.!? n of
  Just ty' -> if ty == ty' then return unifier else throwError $ UnifierInsertConflict n ty unifier
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
  _ -> throwError $ ConstraintsConflict c
  where
    occurCheck v t@(VariableType _) = v == t
    occurCheck v (ArrowType ty) = occurCheck v (ty ^. #domain) || occurCheck v (ty ^. #codomain)
    occurCheck _ _ = False

-- TODO: infinite loop risk, x = y = z
refineUnifer :: Unifier -> Unifier
refineUnifer sigma = instantiate sigma <$> sigma

instantiate :: Unifier -> Type -> Type
instantiate unifier ty = leaveEff $ runReaderDef (instantiate' ty) unifier
instantiate' :: Type -> Eff '[ReaderDef Unifier] Type
instantiate' (VariableType name) = do
  sigma <- ask
  case sigma Map.!? name of
    Just ty -> instantiate' ty
    Nothing -> return $ VariableType name
instantiate' (ArrowType ty') = do
  domain <- instantiate' $ ty' ^. #domain
  codomain <- instantiate' $ ty' ^. #codomain
  return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
instantiate' (PairType ty1 ty2) = PairType <$> instantiate' ty1 <*> instantiate' ty2
instantiate' t = return t

unify' :: Constraints -> Eff '[EitherDef UnifyError] Unifier
unify' = fmap refineUnifer . unify

typeOf :: NamingContext -> UnNamedTerm -> Eff '[EitherDef TypingError] Type
typeOf ctx t = fmap fst . mapEitherDef  ReconstructionError $ evalStateEff @"fresh"   (evalStateEff @"context" (reconstruction t) ctx) 0

typeOf' :: NamingContext -> NamedTerm -> Either Errors Type
typeOf' ctx t = leaveEff . runEitherDef $ do
  t' <- mapEitherDef UnNameError $ evalStateEff @"context" (unName t) ctx
  mapEitherDef TypingError $ typeOf ctx t'