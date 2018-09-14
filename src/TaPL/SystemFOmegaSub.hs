{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels      #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module TaPL.SystemFOmegaSub where

import RIO
import qualified RIO.Vector as V

import Control.Lens hiding ((:>), (^.))
import Control.Monad.Error.Class
import Data.Extensible
import Data.Extensible.Effect.Default

import TaPL.NameLess

import SString
import MapLeftEff
-- import qualified Debug.Trace as D



data Errors = 
    NameLessError NameLessErrors
  | TypingError TypingError
  deriving (Eq)
instance Show Errors where
  show (NameLessError e) = "NameLess Error: " ++ show e
  show (TypingError e) = "Typing Error: " ++ show e


class IndexOperation (f :: Bool -> *) where
  indexMap :: DeBrujinIndex -> f 'False -> Eff ["onvar" >: ReaderEff (DeBrujinIndex -> NameLessVariable -> f 'False), "ontype" >: ReaderEff (DeBrujinIndex -> UnNamedType -> UnNamedType)] (f 'False)
class IndexOperation f => IndexShift (f :: Bool -> *) where
  indexShift :: DeBrujinIndex -> f 'False -> f 'False
  indexShift = flip indexShift' 0
  indexShift' :: DeBrujinIndex -> DeBrujinIndex -> f 'False -> f 'False
class IndexOperation f => Substitution (f :: Bool -> *) (g :: Bool -> *) where
  subst :: DeBrujinIndex -> g 'False -> f 'False -> f 'False
betaReduction :: (IndexShift f, IndexShift g, Substitution f g) => g 'False -> f 'False -> f 'False
betaReduction s t = indexShift (-1) $ subst 0 (indexShift 1 s) t
leaveBetaReduction :: (NameLess f 'True, NameLess f 'False, NameLess g 'True, IndexShift f, IndexShift g, Substitution f g) => NamingContext -> g 'True -> f 'True -> Either NameLessErrors (f 'True)
leaveBetaReduction ctx s t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ do
  s1 <- mapLeftDef UnNameError $ unName s
  t1 <- mapLeftDef UnNameError $ unName t
  let t' = betaReduction s1 t1
  mapLeftDef RestoreNameError $ restoreName t'



data Kind = 
    StarKind 
  | ArrowKind (Record '["domain" :> Kind, "codomain" :> Kind])
  deriving (Eq)
instance Show Kind where
  show StarKind = "*"
  show (ArrowKind k) = concat ["(", show (k ^. #domain), " -> ", show (k ^. #codomain), ")"]

data Type a =
    TopType
  | VariableType (Named a) 
  | ArrowType (Record '["domain" :> Type a, "codomain" :> Type a])
  | UniversalType (Record '["name" :> SString, "bound" :> Type a , "body" :> Type a])
  | AbstractionType (Record '["name" :> SString, "kind" :> Kind, "body" :> Type a])
  | ApplicationType (Record '["function" :> Type a, "argument" :> Type a])
deriving instance (Eq (Named a), Eq (Type a)) => Eq (Type a)
instance (Show (Named a), Show (Type a)) => Show (Type a) where
  show TopType = "T"
  show (VariableType ty)  = show ty
  show (ArrowType ty)     = concat ["(", show (ty ^. #domain), " -> ", show (ty ^. #codomain), ")"]
  show (UniversalType ty) = concat ["(∀", show (ty ^. #name), "<:", show (ty ^. #bound) ,".", show (ty ^. #body), ")"]
  show (AbstractionType ty) = concat ["λ", show (ty ^. #name), "::", show (ty ^. #kind), ".", show (ty ^. #body)]
  show (ApplicationType ty) = concat ["(", show (ty ^. #function), " ", show (ty ^. #argument), ")"]
type NamedType = Type 'True
type UnNamedType = Type 'False

instance FindVar Type 'True where
  findvar _ ctx x = V.findIndex isBound ctx
    where
      isBound (x', VariableTypeBind) | x == x' = True
      isBound _ = False
instance FindVar Type 'False where
  findvar _ ctx x = fst <$> ctx V.!? x
instance FindVar Type a => NameLess Type a where
  nameless TopType = return TopType
  nameless (VariableType x) = do
    ctx <- ask
    case findvar (Proxy :: Proxy Type) ctx x of
      Just x' -> return $ VariableType x'
      Nothing -> throwError $ MissingTypeVariableInNamingContext x ctx
  nameless (ArrowType ty) = do
    domain <- nameless $ ty ^. #domain
    codomain <- nameless $ ty ^. #codomain
    return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
  nameless (UniversalType ty) = do
    let x  = ty ^. #name
    bound <- nameless $ ty ^. #bound
    body <- local (V.cons (x, VariableTypeBind)) $ nameless (ty ^. #body)
    return . UniversalType $ #name @= x <: #bound @= bound <: #body @= body <: nil
  nameless (AbstractionType ty) = do
    let x = ty ^. #name
    body <- local (V.cons (x, VariableTypeBind)) $ nameless (ty ^. #body)
    return . AbstractionType $ #name @= x <: #kind @= ty ^. #kind <: #body @= body <: nil
  nameless (ApplicationType ty) = do
    t1 <- nameless $ ty ^. #function
    t2 <- nameless $ ty ^. #argument
    return . ApplicationType $ #function @= t1 <: #argument @= t2 <: nil
instance IndexOperation Type where
  indexMap _ TopType = return TopType
  indexMap c (VariableType x) = asksEff #onvar (\onvar -> onvar c x)
  indexMap c (ArrowType ty) = do
    domain <- indexMap c $ ty ^. #domain
    codomain <- indexMap c $ ty ^. #codomain
    return . ArrowType $ ty & #domain .~ domain & #codomain .~ codomain
  indexMap c (UniversalType ty) = do 
    bound <- indexMap c $ ty ^. #bound
    body <- indexMap (c+1) $ ty ^. #body
    return . UniversalType $ ty & #bound .~ bound & #body .~ body
  indexMap c (AbstractionType ty) = do
    body <- indexMap (c+1) $ ty ^. #body
    return . AbstractionType $ ty & #body .~ body
  indexMap c (ApplicationType ty) = do
    f <- indexMap c $ ty ^. #function
    arg <- indexMap c $ ty ^. #argument
    return . ApplicationType $ ty & #function .~ f & #argument .~ arg
instance IndexShift Type where
  indexShift' d c ty = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap c ty) onvar) undefined
    where
      onvar n var | var < n = VariableType var
                  | otherwise = VariableType $ var + d
instance Substitution Type Type where
  subst j s t = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap j t) onvar) undefined
    where
      onvar n var | var == n = indexShift n s
                  | otherwise = VariableType var
                

data Term a =
    ConstTerm SString
  | VariableTerm (Named a)
  | AbstractionTerm (Record '["name" :> SString, "type" :> Type a, "body" :> Term a])
  | ApplicationTerm (Record '["function" :> Term a, "argument" :> Term a])
  | TypeAbstractionTerm (Record '["name" :> SString, "bound" :> Type a, "body" :> Term a])
  | TypeApplicationTerm (Record '["term" :> Term a, "type" :> Type a])
deriving instance (Eq (Term a), Eq (Type a), Eq (Named a)) => Eq (Term a)
instance (Show (Named a), Show (Type a), Show (Term a)) => Show (Term a) where
  show (ConstTerm s) = show s
  show (VariableTerm t) = show t
  show (AbstractionTerm t) = concat ["λ", show (t ^. #name), ":", show (t ^. #type), ".", show (t ^. #body)]
  show (ApplicationTerm t) = concat ["(", show (t ^. #function), " ", show (t ^. #argument), ")"]
  show (TypeAbstractionTerm t) = concat ["λ", show (t ^. #name), "<:", show (t ^. #bound), ".", show (t ^. #body)]
  show (TypeApplicationTerm t) = concat [show (t ^. #term), " [", show (t ^. #type) ,"]"]
type NamedTerm = Term 'True
type UnNamedTerm = Term 'False

instance FindVar Term 'True where
  findvar _ ctx x = V.findIndex isBound ctx
    where
      isBound (x', VariableTermBind) | x == x' = True
      isBound _ = False
instance FindVar Term 'False where
  findvar _ ctx x = fst <$> ctx V.!? x
instance (FindVar Term a, FindVar Type a) => NameLess Term a where
  nameless (ConstTerm s) = return $ ConstTerm s
  nameless (VariableTerm x) = do
    ctx <- ask
    case findvar (Proxy :: Proxy Term) ctx x of
      Just x'  -> return $ VariableTerm x'
      Nothing -> throwError $ MissingVariableInNamingContext x ctx
  nameless (AbstractionTerm t) = do
    let x  = t ^. #name
    ty <- nameless $ t ^. #type
    body <- local (V.cons (x, VariableTermBind)) $ nameless (t ^. #body)
    return . AbstractionTerm $ #name @= x <: #type @= ty <: #body @= body <: nil
  nameless (ApplicationTerm t) = do
    t1 <- nameless $ t ^. #function
    t2 <- nameless $ t ^. #argument
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil
  nameless (TypeAbstractionTerm t) = do
    bound <- nameless $ t ^. #bound
    body <- local (V.cons (t ^. #name, VariableTypeBind)) $ nameless (t ^. #body)
    return . TypeAbstractionTerm $ #name @= t ^. #name <: #bound @= bound <: #body @= body <: nil
  nameless (TypeApplicationTerm t) = do
    term <- nameless $ t ^. #term
    ty   <- nameless $ t ^. #type
    return . TypeApplicationTerm $ #term @= term <: #type @= ty <: nil
instance IndexOperation Term where
  indexMap _ t@(ConstTerm _) = return t
  indexMap c (VariableTerm t) = asksEff #onvar (\onvar -> onvar c t)
  indexMap c (AbstractionTerm t) = do
    ty <- asksEff #ontype (\ontype -> ontype c $ t ^. #type)
    body <- indexMap (c+1) $ t ^. #body
    return . AbstractionTerm $ t & #type .~ ty & #body .~ body
  indexMap c (ApplicationTerm t) = do
    f <- indexMap c $ t ^. #function
    arg <- indexMap c $ t ^. #argument
    return . ApplicationTerm $ t & #function .~ f & #argument .~ arg
  indexMap c (TypeAbstractionTerm t) = do
    bound <- asksEff #ontype (\ontype -> ontype c $ t ^. #bound)
    body <- indexMap (c+1) $ t ^. #body
    return . TypeAbstractionTerm $ t & #bound .~ bound & #body .~ body
  indexMap c (TypeApplicationTerm t) = do
    term <- indexMap c $ t ^. #term
    ty <- asksEff #ontype (\ontype -> ontype c $ t ^. #type)
    return . TypeApplicationTerm $ t & #term .~ term & #type .~ ty
instance IndexShift Term where
  indexShift' d c t = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap c t) onvar) ontype
    where
      onvar n var | var < n = VariableTerm var
                  | otherwise = VariableTerm $ var + d
      ontype = indexShift' d
instance Substitution Term Term where
  subst j s t = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap j t) onvar) ontype
    where
      onvar n var | var == n = indexShift n s
                  | otherwise = VariableTerm var
      ontype _ ty = ty
instance Substitution Term Type where
  subst j s t = leaveEff $ runReaderEff @"ontype" (runReaderEff @"onvar" (indexMap j t) onvar) ontype
    where
      onvar _ var = VariableTerm var
      ontype n ty = subst n s ty

isVal :: UnNamedTerm -> Bool
isVal (ConstTerm _) = True
isVal (AbstractionTerm _) = True
isVal (TypeAbstractionTerm _) = True
isVal _ = False

eval1 :: UnNamedTerm -> Maybe UnNamedTerm
eval1 (ApplicationTerm t) = case t ^. #function of
  (AbstractionTerm t') | isVal (t ^. #argument) -> Just $ betaReduction (t ^. #argument) (t' ^. #body)
  v1 | isVal v1 -> (\t2' -> ApplicationTerm $ t & #argument .~ t2') <$> eval1 (t ^. #argument)
  t1 -> (\t1' -> ApplicationTerm $ t & #function .~ t1') <$> eval1 t1
eval1 (TypeApplicationTerm t) = case t ^. #term of
  (TypeAbstractionTerm t') -> Just $ betaReduction (t ^. #type) (t' ^. #body)
  t1 -> (\t1' -> TypeApplicationTerm $ t & #term .~ t1') <$> eval1 t1
eval1 _ = Nothing

eval :: UnNamedTerm -> UnNamedTerm
eval t = case eval1 t of
  Just t' -> eval t'
  Nothing -> t

leaveEval :: NamingContext -> NamedTerm -> Either NameLessErrors NamedTerm
-- leaveEval ctx t = mapLeft UnNameError (leaveUnName ctx t) >>= mapLeft RestoreNameError . leaveRestoreName ctx . eval
leaveEval ctx t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ mapLeftDef UnNameError (unName t) >>= mapLeftDef RestoreNameError . restoreName . eval

type TypingContext = Vector (SString, TypedBinding)
typingContextToNamingContext :: TypingContext -> NamingContext
typingContextToNamingContext = fmap (& _2 %~ f)
  where
    f (TypedConstTermBind _) = ConstTermBind
    f (TypedVariableTermBind _) = VariableTermBind
    f TypedConstTypeBind = ConstTypeBind
    f (TypedVariableTypeBind _) = VariableTypeBind
data TypedBinding = 
    TypedConstTermBind UnNamedType
  | TypedVariableTermBind UnNamedType 
  | TypedConstTypeBind 
  | TypedVariableTypeBind UnNamedType
  deriving (Show, Eq)
data KindingError =
    MissingTypeVariableInNamingContextWhileKinding
  | UnMatchedKindArrowType
  | UnMatchedKindUniversalType
  | UnMatchedKindApplicationType
  deriving (Show, Eq)
kinding :: UnNamedType -> Eff '[EitherDef KindingError, ReaderDef TypingContext] Kind
kinding TopType = return StarKind
kinding (VariableType x) = do
  ctx <- ask
  case snd <$> ctx V.!? x of
    Just (TypedVariableTypeBind ty) -> kinding ty
    _ -> throwError MissingTypeVariableInNamingContextWhileKinding
kinding (ArrowType ty) = do
  domain <- kinding $ ty ^. #domain
  codomain <- kinding $ ty ^. #codomain
  if domain == StarKind && codomain == StarKind
    then return StarKind
    else throwError UnMatchedKindArrowType
kinding (UniversalType ty) = do
  body <- local (V.cons (ty ^. #name, TypedVariableTypeBind (ty ^. #bound))) $ kinding (ty ^. #body)
  if body == StarKind
    then return StarKind
    else throwError UnMatchedKindUniversalType
kinding (AbstractionType ty) = do
  let k = ty ^. #kind
      top = topOf k
  codomain <- local (V.cons (ty ^. #name, TypedVariableTypeBind top)) $ kinding (ty ^. #body)
  return . ArrowKind $ #domain @= k <: #codomain @= codomain <: nil
kinding (ApplicationType ty) = do
  k1 <- kinding $ ty ^. #function
  k2 <- kinding $ ty ^. #argument
  case k1 of
    ArrowKind k | k ^. #domain == k2 -> return $ k ^. #codomain
    _ -> throwError UnMatchedKindApplicationType

topOf :: Kind -> Type a
topOf StarKind = TopType
topOf (ArrowKind k) = AbstractionType $ #name @= "_" <: #kind @= k ^. #domain <: #body @= topOf (k ^. #codomain) <: nil

data TypingError = 
  --   MissingDeclarationInNamingContext SString TypingContext
  -- | MissingVariableTypeInNamingContext DeBrujinIndex TypingContext
  -- | NotMatchedTypeNatType NamedTerm NamedType
  -- | NotMatchedTypeArrowType NamedTerm NamedType NamedTerm NamedType 
  -- | NotMatchedTypeArrowType
  -- | NotMatchedTypeProjectionNotRecord
  -- | NotMatchedTypeProjectionLabelMissing
  -- | NotMatchedTypeUniversalType
  -- | NotMatchedTypeExistType NamedTerm NamedType
  -- | NotMatchedTypeExistTypeInstantiate
  -- | RestoreNameErrorWhileTypingError RestoreNameError
    MissingDeclarationInNamingContext
  | MissingVariableTypeInNamingContext
  | UnMatchedTypeNatType
  | UnMatchedTypeArrowType
  | UnMatchedTypeArrowTypeKindIsNotStar
  | UnMatchedTypeArrowTypeSubType
  | UnMatchedTypeProjectionLabelMissing
  | UnMatchedTypeUniversalType
  | UnMatchedTypeUniversalTypeSubType
  | UnMatchedTypeExistType
  | UnMatchedTypeExistTypeInstantiate
  | RestoreNameErrorWhileTypingError RestoreNameError
  | KindingError KindingError
  | PromotingError PromotingError
  deriving (Show, Eq)
-- instance Show TypingError where
--   show (MissingDeclarationInNamingContext name ctx) = concat ["missing constant declaration in naming context: constant: ", show name, ", NamingContext: ", show ctx]
--   show (MissingVariableTypeInNamingContext name ctx) = concat ["missing variable in naming context: variable: ", show name, ", NamingContext: ", show ctx]
--   show (NotMatchedTypeNatType t ty) = concat ["failed to apply succ: t = ", show t, ": ", show ty]
--   show (NotMatchedTypeArrowType t1 ty1 t2 ty2) = concat ["failed to apply: t1 = ", show t1, ": ", show ty1, ", t2 = ", show t2, ": ", show ty2]
--   -- show (NotMatchedTypeArrowType) = "NotMatchedTypeArrowType"
--   show (NotMatchedTypeProjectionNotRecord) = "NotMatchedTypeProjectionNotRecord"
--   show (NotMatchedTypeProjectionLabelMissing) = "NotMatchedTypeProjectionLabelMissing"
--   show (NotMatchedTypeUniversalType) = "NotMatchedTypeUniversalType"
--   show (NotMatchedTypeExistType term ty) = concat ["Expected type: ExistType, Actual type: ", show ty, ", term = ", show term]
--   show (NotMatchedTypeExistTypeInstantiate) = "NotMatchedTypeExistTypeInstantiate"
--   show (RestoreNameErrorWhileTypingError e) = "RestorName Error While Typing Error: " ++ show e


typing :: UnNamedTerm -> Eff '[EitherDef TypingError, ReaderDef TypingContext] UnNamedType
typing (ConstTerm s) = do
  bind <- asks $ fmap (^. _2) . V.find ((==) s . (^. _1))
  case bind of
    Just (TypedConstTermBind ty) -> return ty
    _ -> throwError MissingDeclarationInNamingContext
typing (VariableTerm x) = do
  ctx <- ask
  case ctx V.!? x of
    Just (_, TypedVariableTermBind ty) -> return $ indexShift (x+1) ty
    _ -> throwError MissingVariableTypeInNamingContext
typing (AbstractionTerm t) = do
  k <- mapLeftDef KindingError . kinding $ t ^. #type
  if k /= StarKind
    then throwError UnMatchedTypeArrowTypeKindIsNotStar
    else do
      let domain = t ^. #type
      codomain <- local (V.cons (t ^. #name, TypedVariableTermBind domain)) $ typing (t ^. #body)
      return . ArrowType $ #domain @= domain <: #codomain @= indexShift (-1) codomain <: nil
typing (ApplicationTerm t) = do
  ty1 <- typing $ t ^. #function
  ty2 <- typing $ t ^. #argument
  case ty1 of
    ArrowType ty1' -> do
      m <- castEff . runEitherDef $ ty2 `isSubTypeOf` (ty1' ^. #domain)
      case m of
        Right b -> if b
          then return $ ty1' ^. #codomain
          else throwError UnMatchedTypeArrowTypeSubType
        Left e -> throwError $ PromotingError e
    _ -> throwError UnMatchedTypeArrowType
typing (TypeAbstractionTerm t) = do
  let x = t ^. #name
      bound = t ^. #bound
  body <- local (V.cons (x, TypedVariableTypeBind bound)) $ typing (t ^. #body)
  return . UniversalType $ #name @= x <: #bound @= bound <: #body @= body <: nil
typing (TypeApplicationTerm t) = do
  term <- typing $ t ^. #term
  term' <- asks (leaveEff . runReaderDef (expose term)) 
  case term' of
    UniversalType ty -> do
      m <- castEff . runEitherDef $ (t ^. #type) `isSubTypeOf` (ty ^. #bound)
      case m of
        Right b -> if b 
          then return $ betaReduction (t ^. #type) (ty ^. #body)
          else throwError UnMatchedTypeUniversalTypeSubType
        Left e -> throwError $ PromotingError e
    _ -> throwError UnMatchedTypeUniversalType
 

expose :: UnNamedType -> Eff '[ReaderDef TypingContext] UnNamedType
expose ty = fmap (either (const ty) id) . runEitherDef $ promoteVariable (normalize ty) 

data PromotingError = 
    MissingTypeVariableInNamingContextWhilePromoting DeBrujinIndex TypingContext
  | UnMatchedPromoting
  deriving (Eq)
instance Show PromotingError where
  show (MissingTypeVariableInNamingContextWhilePromoting i ctx) = concat ["missing type variable in naming context: variable = ", show i, ", context = ", show ctx]
  show UnMatchedPromoting = "UnMatchedPromoting"

promoteVariable :: UnNamedType -> Eff '[EitherDef PromotingError, ReaderDef TypingContext] UnNamedType
promoteVariable (VariableType x) = do
  ctx <- ask
  case snd <$> ctx V.!? x of
    Just (TypedVariableTypeBind ty') -> return $ indexShift (x+1) ty'
    _ -> throwError $ MissingTypeVariableInNamingContextWhilePromoting x ctx
promoteVariable (ApplicationType ty) = (\ty' -> ApplicationType $ ty & #function .~ ty') <$> promoteVariable (ty ^. #function)
promoteVariable _ = throwError UnMatchedPromoting

-- perform betaReduction on the left of type application
normalize :: UnNamedType -> UnNamedType
normalize (ApplicationType ty) = case normalize $ ty ^. #function of
    AbstractionType ty' -> normalize $ betaReduction (ty ^. #argument) (ty' ^. #body)
    f -> ApplicationType $ ty & #function .~ f
normalize ty = ty
leaveNormalize :: NamingContext -> NamedType -> Either NameLessErrors NamedType
leaveNormalize ctx ty = leaveEff . (`runReaderDef` ctx) . runEitherDef $ mapLeftDef UnNameError (unName ty) >>= mapLeftDef RestoreNameError . restoreName . normalize

isSubTypeOf :: UnNamedType -> UnNamedType -> Eff '[EitherDef PromotingError, ReaderDef TypingContext] Bool
isSubTypeOf ty1 ty2 | ty1 `isEquivalentTo` ty2 = return True
isSubTypeOf ty1 ty2 = case (normalize ty1, normalize ty2) of
  (_, TopType) -> return True
  (ty1'@(VariableType _), ty2') -> promoteVariable ty1' >>= (`isSubTypeOf` ty2')
  (ArrowType ty1', ArrowType ty2') -> (&&) <$> ((ty1' ^. #domain) `isSubTypeOf` (ty2' ^. #domain)) <*> ((ty1' ^. #codomain) `isSubTypeOf` (ty2' ^. #codomain))
  (UniversalType ty1', UniversalType ty2') -> do
    let bound1 = ty1' ^. #bound
        bound2 = ty2' ^. #bound
    b1 <- (&&) <$> (bound1 `isSubTypeOf` bound2) <*> (bound2 `isSubTypeOf` bound1) -- equivalent??
    b2 <- local (V.cons (ty1' ^. #name <> "_" <> ty2' ^. #name, TypedVariableTypeBind bound1)) $ (ty1' ^. #body) `isSubTypeOf` (ty2' ^. #body)
    return $ b1 && b2
  (AbstractionType ty1', AbstractionType ty2') -> do
    let k = ty1' ^. #kind
    b <- local (V.cons (ty1' ^. #name <> "_" <> ty2' ^. #name, TypedVariableTypeBind (topOf k))) $ (ty1' ^. #body) `isSubTypeOf` (ty2' ^. #body)
    return $ (k == ty2' ^. #kind) && b
  (ty1'@(ApplicationType _), ty2') -> promoteVariable ty1' >>= (`isSubTypeOf` ty2')
  _ -> return False

isEquivalentTo :: UnNamedType -> UnNamedType -> Bool
isEquivalentTo ty1 ty2 = case (normalize ty1, normalize ty2) of
  (TopType, TopType) -> True
  (VariableType x, VariableType y) -> x == y
  (ArrowType ty1', ArrowType ty2') -> ((ty1' ^. #domain) `isEquivalentTo` (ty2' ^. #domain)) && ((ty1' ^. #codomain) `isEquivalentTo` (ty2' ^. #codomain))
  (UniversalType ty1', UniversalType ty2') -> ((ty1' ^. #bound) `isEquivalentTo` (ty2' ^. #bound)) && ((ty1' ^. #body) `isEquivalentTo` (ty2' ^. #body))
  (AbstractionType ty1', AbstractionType ty2') -> (ty1' ^. #kind == ty2' ^. #kind) && ((ty1' ^. #body) `isEquivalentTo` (ty2' ^. #body))
  (ApplicationType ty1', ApplicationType ty2') -> ((ty1' ^. #function) `isEquivalentTo` (ty2' ^. #function)) && ((ty1' ^. #argument) `isEquivalentTo` (ty2' ^. #argument))
  _ -> False

leaveIsSubTypeOf :: TypingContext -> NamedType -> NamedType -> Either Errors Bool
leaveIsSubTypeOf ctx ty1 ty2 = do
  ty1' <- mapLeft (NameLessError . UnNameError) $ leaveUnName (typingContextToNamingContext ctx) ty1
  ty2' <- mapLeft (NameLessError . UnNameError) $ leaveUnName (typingContextToNamingContext ctx) ty2
  mapLeft (TypingError . PromotingError) . leaveEff $ runReaderDef (runEitherDef $ ty1' `isSubTypeOf` ty2') ctx
