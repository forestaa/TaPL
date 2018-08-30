{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}


module TaPL.RecEqui where


import RIO
import qualified RIO.Set as Set
import qualified RIO.Vector as V

import Control.Monad.Error.Class
import Control.Monad.State.Strict

import Control.Lens hiding ((:>), (^.))
import Data.Extensible
import Data.Extensible.Effect.Default

import SString

mapError :: (e -> e') -> Eff '[EitherDef e] a -> Eff '[EitherDef e'] a 
mapError f m = do
  ret <- castEff $ runEitherDef m
  case ret of
    Right a -> return a
    Left e -> throwError $ f e

type DeBrujinIndex = Int

type family Named (a :: Bool) where
  Named 'True  = SString
  Named 'False = DeBrujinIndex

leaveEitherDef :: Eff '[EitherDef e] a -> Either e a
leaveEitherDef = leaveEff . runEitherDef
leaveEvalStateDef :: s -> Eff '[StateDef s] a -> a
leaveEvalStateDef s = leaveEff . flip evalStateDef s
leaveEitherDefEvalStateDef :: s -> Eff '[StateDef s, EitherDef e] a -> Either e a
leaveEitherDefEvalStateDef s = leaveEff . runEitherDef . flip evalStateDef s

class UnName (f :: Bool -> *) where
  unName      :: f 'True -> Eff '[StateDef NamingContext, EitherDef UnNameError] (f 'False)
  restoreName :: f 'False -> Eff '[StateDef NamingContext, EitherDef RestoreNameError] (f 'True)

data Type a = 
    PrimitiveType SString
  | VariableType (Record '[ "id" :> Named a ])
  | ArrowType (Record '[ "domain" >: Type a, "codomain" >: Type a ])
  | RecursionType (Record '[ "name" >: SString, "body" >: Type a ])
type NamedType = Type 'True
type UnNamedType = Type 'False

data Term a =
    ConstTerm SString
  | VariableTerm (Record '[ "id" :> Named a ])
  | AbstractionTerm (Record '[ "name" :> SString, "type" :> Type a, "body" :> Term a ])
  | ApplicationTerm (Record '[ "function" :> Term a, "argument" :> Term a ])
type NamedTerm = Term 'True
type UnNamedTerm = Term 'False

type Declarations = [(SString, Declaration)]
data Declaration = ConstTermDec NamedType | ConstTypeDec deriving (Show)
type NamingContext = Vector (SString, Binding)
data Binding = ConstTermBind UnNamedType | VariableTermBind UnNamedType | ConstTypeBind | VariableTypeBind deriving (Show, Eq)
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
data TypingError = 
    MissingDeclarationInNamingContext SString NamingContext
  | MissingVariableTypeInNamingContext DeBrujinIndex NamingContext
  | NotMatchedTypeArrowType NamedTerm NamedType NamedTerm NamedType 
  | RestoreNameErrorWhileTypingError RestoreNameError
  deriving (Eq)


deriving instance (Eq (Type a), Eq (Named a)) => Eq (Type a)
deriving instance (Eq (Term a), Eq (Type a), Eq (Named a)) => Eq (Term a)
deriving instance Eq (Named a) => Eq (NamingContextError a)
deriving instance (Ord (Type a), Ord (Named a)) => Ord (Type a)
deriving instance (Ord (Term a), Ord (Type a), Ord (Named a)) => Ord (Term a)

instance (Show (Named a), Show (Type a)) => Show (Type a) where
  show (PrimitiveType ty) = show ty
  show (VariableType ty)  = show (ty ^. #id)
  show (ArrowType ty)     = concat ["(", show (ty ^. #domain), " -> ", show (ty ^. #codomain), ")"]
  show (RecursionType ty) = concat ["(μ", show (ty ^. #name), ".", show (ty ^. #body), ")"]

instance (Show (Named a), Show (Type a), Show (Term a)) => Show (Term a) where
  show (ConstTerm s) = show s
  show (VariableTerm t) = show (t ^. #id)
  show (AbstractionTerm t) = concat ["(λ", show (t ^. #name), ":", show (t ^. #type), ".", show (t ^. #body), ")"]
  show (ApplicationTerm t) = concat ["(", show (t ^. #function), " ", show (t ^. #argument), ")"]

instance Show Errors where
  show (UnNameError e) = "UnName Error: " ++ show e
  show (TypingError e) = "Typing Error: " ++ show e
  show (RestoreNameError e) = "RestoreName Error: " ++ show e
instance Show (Named a) => Show (NamingContextError a) where
  show (MissingVariableInNamingContext name ctx) = concat ["missing variable in naming context: variable: ", show name, ", NamingContext: ", show ctx]
  show (MissingTypeVariableInNamingContext name ctx) = concat ["missing type variable in naming context: type variable: ", show name, ", NamingContext: ", show ctx]
instance Show TypingError where
  show (MissingDeclarationInNamingContext name ctx) = concat ["missing constant declaration in naming context: constant: ", show name, ", NamingContext: ", show ctx]
  show (MissingVariableTypeInNamingContext name ctx) = concat ["missing variable in naming context: variable: ", show name, ", NamingContext: ", show ctx]
  show (NotMatchedTypeArrowType t1 ty1 t2 ty2) = concat ["failed to apply: t1 = ", show t1, ": ", show ty1, ", t2 = ", show t2, ": ", show ty2]
  show (RestoreNameErrorWhileTypingError e) = "RestorName Error While Typing Error: " ++ show e

declarationsToContext :: Declarations -> Eff '[EitherDef UnNameError] NamingContext
declarationsToContext ds = (V.++) ctx <$> traverse ((\(a, b) -> (,) a <$> b) . (& _2 %~ (fmap ConstTermBind . flip evalStateDef ctx . unName))) termdec
  where
    isTypeDec (_, ConstTypeDec) = True
    isTypeDec _ = False
    extractType (ConstTermDec ty) = ty
    extractType b = error $ "declarationsToContext: extractType: unexpected pattern: " ++ show b
    (typedec, termdec) = (& _2 %~ fmap (& _2 %~ extractType)) $ V.partition isTypeDec $ V.fromList ds
    ctx = (& _2 .~ ConstTypeBind) <$> typedec

instance UnName Type where
  unName (PrimitiveType ty) = return $ PrimitiveType ty
  unName (VariableType ty) =  do
    maybei <- V.findIndex isBound <$> get
    case maybei of
      Just i  -> return . VariableType $ #id @= i <: nil
      Nothing -> do
        ctx <- get
        throwError $ MissingTypeVariableInNamingContext (ty ^. #id) ctx
    where
      isBound (x, VariableTypeBind) | x == ty ^. #id = True
      isBound _ = False
  unName (ArrowType ty) = do
    domain <- unName $ ty ^. #domain
    codomain <- unName $ ty ^. #codomain
    return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
  unName (RecursionType ty) = do
    let x  = ty ^. #name
        body = ty ^. #body
    ctx <- modify (V.cons (x, VariableTypeBind)) >> get
    body' <- castEff $ evalStateDef (unName body) ctx
    return . RecursionType $ #name @= x <: #body @= body' <: nil

  restoreName (PrimitiveType ty) = return $ PrimitiveType ty
  restoreName (VariableType ty) = do
    ctx <- get
    case ctx V.!? (ty ^. #id) of
      Just (name, _) -> return . VariableType $ #id @= name <: nil
      Nothing        -> throwError $ MissingTypeVariableInNamingContext (ty ^. #id) ctx
  restoreName (ArrowType ty) = do
    domain <- restoreName $ ty ^. #domain
    codomain <- restoreName $ ty ^. #codomain
    return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
  restoreName (RecursionType ty) = do
    let x  = ty ^. #name
        body = ty ^. #body
    ctx <- modify (V.cons (x, VariableTypeBind)) >> get
    body' <- castEff $ evalStateDef (restoreName body) ctx
    return . RecursionType $ #name @= x <: #body @= body' <: nil


instance UnName Term where
  unName (ConstTerm s) = return $ ConstTerm s
  unName (VariableTerm t) = do
    maybei <- V.findIndex isBound <$> get
    case maybei of
      Just i  -> return . VariableTerm $ #id @= i <: nil
      Nothing -> do
        ctx <- get
        throwError $ MissingVariableInNamingContext (t ^. #id) ctx
    where
      isBound (x, VariableTermBind _) | x == t ^. #id = True
      isBound _ = False
  unName (AbstractionTerm t) = do
    let x  = t ^. #name
        ty = t ^. #type
    ctx <- get
    ty' <- castEff $ evalStateDef (unName ty) ctx
    newctx <- modify (V.cons (x, VariableTermBind ty')) >> get
    t' <- castEff $ evalStateDef (unName $ t ^. #body) newctx
    return . AbstractionTerm $ #name @= x <: #type @= ty' <: #body @= t' <: nil
  unName (ApplicationTerm t) = do
    ctx <- get
    t1 <- castEff $ evalStateDef (unName $ t ^. #function) ctx
    t2 <- castEff $ evalStateDef (unName $ t ^. #argument) ctx
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil

  restoreName (ConstTerm s) = return $ ConstTerm s
  restoreName (VariableTerm t) = do
    ctx <- get 
    case ctx V.!? (t ^. #id) of
      Just (name, _) -> return $ VariableTerm $ #id @= name <: nil
      Nothing -> get >>= throwError . MissingVariableInNamingContext (t ^. #id)
  restoreName (AbstractionTerm t) = do
    let x  = t ^. #name
        ty = t ^. #type
    ctx <- get
    newctx <- modify (V.cons (x, VariableTermBind ty)) >> get
    ty' <- castEff $ evalStateDef (restoreName ty) ctx
    t'  <- castEff $ evalStateDef (restoreName $ t ^. #body) newctx
    return . AbstractionTerm $ #name @= x <: #type @= ty' <: #body @= t' <: nil
  restoreName (ApplicationTerm t) = do
    ctx <- get
    t1 <- castEff $ evalStateDef (restoreName $ t ^. #function) ctx
    t2 <- castEff $ evalStateDef (restoreName $ t ^. #argument) ctx
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil


class IndexShift (f :: Bool -> *) where
  indexShift :: DeBrujinIndex -> f 'False -> f 'False
instance IndexShift Type where
  indexShift d = walk 0
    where
      walk _ (PrimitiveType ty) = PrimitiveType ty
      walk c (VariableType ty) 
        | ty ^. #id < c = VariableType ty 
        | otherwise =  VariableType $ ty & #id +~ d
      walk c (ArrowType ty) = ArrowType $ ty & #domain %~ walk c & #codomain %~ walk c
      walk c (RecursionType ty) = RecursionType $ ty & #body %~ walk (c+1)

class Substitution (f :: Bool -> *) where
  subst :: DeBrujinIndex -> f 'False -> f 'False -> f 'False
instance Substitution Type where
  subst _ _ (PrimitiveType ty) = PrimitiveType ty
  subst j s (VariableType ty)
    | ty ^. #id == j = indexShift j s
    | otherwise = VariableType ty
  subst j s (ArrowType ty) = ArrowType $ ty & #domain %~ subst j s & #codomain %~ subst j s
  subst j s (RecursionType ty) = RecursionType $ ty & #body %~ subst (j+1) s

betaReduction :: (IndexShift f, Substitution f) => f 'False -> f 'False -> f 'False
betaReduction s t = indexShift (-1) $ subst 0 (indexShift 1 s) t


typeOf :: UnNamedTerm -> Eff '[StateDef NamingContext, EitherDef TypingError] UnNamedType
typeOf (ConstTerm s) = do
  bind <- fmap (^. _2) . V.find ((==) s . (^. _1)) <$> get
  case bind of
    Just (ConstTermBind ty) -> return ty
    _ -> do
      ctx <- get
      throwError $ MissingDeclarationInNamingContext s ctx
typeOf (VariableTerm t) = do
  ctx <- get
  case ctx V.!? (t ^. #id) of
    Just (_, VariableTermBind ty) -> return ty
    _ -> throwError $ MissingVariableTypeInNamingContext (t ^. #id) ctx
typeOf (AbstractionTerm t) = do
  newctx <- V.cons (t ^. #name, VariableTermBind $ t ^. #type) <$> get
  codomain <- castEff $ evalStateDef (typeOf $ t ^. #body) newctx
  return . ArrowType $ #domain @= t ^. #type <: #codomain @= indexShift (-1) codomain <: nil
typeOf (ApplicationTerm t) = do
  ctx <- get
  ty1 <- castEff $ evalStateDef (typeOf $ t ^. #function) ctx
  ty2 <- castEff $ evalStateDef (typeOf $ t ^. #argument) ctx
  case isArrowable ty1 of
    Just (ArrowType ty1') | leaveEvalStateDef Set.empty (isEquivalent ty2 (ty1' ^. #domain)) -> return $ ty1' ^. #codomain
    _ -> do
      t1'  <- castEff . mapError RestoreNameErrorWhileTypingError $ evalStateDef (restoreName $ t ^. #function) ctx
      ty1' <- castEff . mapError RestoreNameErrorWhileTypingError $ evalStateDef (restoreName ty1) ctx
      t2'  <- castEff . mapError RestoreNameErrorWhileTypingError $ evalStateDef (restoreName $ t ^. #argument) ctx
      ty2' <- castEff . mapError RestoreNameErrorWhileTypingError $ evalStateDef (restoreName ty2) ctx
      throwError $ NotMatchedTypeArrowType t1' ty1' t2' ty2'

isArrowable :: UnNamedType -> Maybe UnNamedType
isArrowable t@(ArrowType _) = Just t
isArrowable t@(RecursionType ty) = isArrowable $ betaReduction t (ty ^. #body)
isArrowable _ = Nothing

isEquivalent :: UnNamedType -> UnNamedType -> Eff '[StateDef (Set.Set (UnNamedType, UnNamedType))] Bool
isEquivalent ty1@(RecursionType ty1') ty2 = do
  s <- modify (Set.insert (ty1, ty2)) >> get
  let ty1'' = betaReduction ty1 (ty1' ^. #body)
  (||) <$> return (Set.member (ty1'', ty2) s) <*> isEquivalent ty1'' ty2
isEquivalent ty1 ty2@(RecursionType ty2') = do
  s <- modify (Set.insert (ty1, ty2)) >> get
  let ty2'' = betaReduction ty2 (ty2' ^. #body)
  (||) <$> return (Set.member (ty1, ty2'') s) <*> isEquivalent ty1 ty2''
isEquivalent (PrimitiveType ty1) (PrimitiveType ty2) = return $ ty1 == ty2
isEquivalent (ArrowType ty1) (ArrowType ty2) = do
  s <- get
  let ty1dom = ty1 ^. #domain
      ty2dom = ty2 ^. #domain
      ty1cod = ty1 ^. #codomain
      ty2cod = ty2 ^. #codomain
      domequi = Set.member (ty1dom, ty2dom) s || leaveEvalStateDef s (isEquivalent ty1dom ty2dom)
      codequi = Set.member (ty1cod, ty2cod) s || leaveEvalStateDef s (isEquivalent ty1cod ty2cod)
  return $ domequi && codequi
isEquivalent _ _ = return False

isEquivalentNamedFromDeclarations :: Declarations -> NamedType -> NamedType -> Either UnNameError Bool
isEquivalentNamedFromDeclarations ds ty1 ty2 = do
  ctx <- leaveEitherDef $ declarationsToContext ds
  isEquivalentNamed ctx ty1 ty2

isEquivalentNamed :: NamingContext -> NamedType -> NamedType -> Either UnNameError Bool
isEquivalentNamed ctx ty1 ty2 = do
  ty1' <- leaveEitherDefEvalStateDef ctx $ unName ty1
  ty2' <- leaveEitherDefEvalStateDef ctx $ unName ty2
  return . leaveEvalStateDef Set.empty $ isEquivalent ty1' ty2'

instance IndexShift Term where
  indexShift d = walk 0
    where
      walk _ t@(ConstTerm _) = t
      walk c (VariableTerm t) 
        | t ^. #id < c = VariableTerm t
        | otherwise = VariableTerm $ t & #id +~ d
      walk c (AbstractionTerm t) = AbstractionTerm $ t & #body %~ walk (c+1)
      walk c (ApplicationTerm t) = ApplicationTerm $ t & #function %~ walk c & #argument %~ walk c
instance Substitution Term where
  subst _ _ t@(ConstTerm _) = t
  subst j s (VariableTerm t) 
    | t ^. #id == j = s
    | otherwise = VariableTerm t
  subst j s (AbstractionTerm t) = AbstractionTerm $ t & #body %~ subst (j+1) (indexShift 1 s)
  subst j s (ApplicationTerm t) = ApplicationTerm $ t & #function %~ subst j s & #argument %~ subst j s

isVal :: UnNamedTerm -> Bool
isVal (ConstTerm _) = True
isVal (AbstractionTerm _) = True
isVal _ = False

unNamedEval1 :: UnNamedTerm -> Maybe UnNamedTerm
unNamedEval1 (ApplicationTerm t) = 
  case t ^. #function of
    AbstractionTerm t' | isVal (t ^. #argument) -> Just $ betaReduction (t ^. #argument) (t' ^. #body)
    v1 | isVal v1 -> do
      t2' <- unNamedEval1 $ t ^. #argument
      return . ApplicationTerm $ t & #argument .~ t2'
    t1 -> do
      t1' <- unNamedEval1 t1
      return . ApplicationTerm $ t & #function .~ t1'
unNamedEval1 _ = Nothing

unNamedEval :: UnNamedTerm -> UnNamedTerm
unNamedEval t =
  case unNamedEval1 t of
    Just t' -> unNamedEval t'
    Nothing -> t

eval :: Declarations -> NamedTerm -> Either Errors (NamedTerm, NamedType)
eval ds t = do
  ctx <- mapLeft UnNameError . leaveEitherDef $ declarationsToContext ds
  t' <- mapLeft UnNameError . leaveEitherDefEvalStateDef ctx $ unName t
  ty <- mapLeft TypingError . leaveEitherDefEvalStateDef ctx $ typeOf t'
  let t'' = unNamedEval t'
  t''' <- mapLeft RestoreNameError . leaveEitherDefEvalStateDef ctx $ restoreName t''
  ty' <- mapLeft RestoreNameError . leaveEitherDefEvalStateDef ctx $ restoreName ty
  return (t''', ty')