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
import qualified RIO.Map as Map
import qualified RIO.Vector as V

import Control.Monad.Error.Class
import Control.Lens hiding ((:>), (^.))
import Data.Extensible
import Data.Extensible.Effect.Default

import MapLeftEff
import SString


type DeBrujinIndex = Int
type NamingContext = Vector (SString, Binding)
data Binding = 
    ConstTermBind
  | VariableTermBind
  | ConstTypeBind 
  | VariableTypeBind 
  deriving (Show, Eq)
data NamingContextError a = 
    MissingVariableInNamingContext (Named a) NamingContext 
  | MissingTypeVariableInNamingContext (Named a) NamingContext
deriving instance Eq (Named a) => Eq (NamingContextError a)
instance Show (Named a) => Show (NamingContextError a) where
  show (MissingVariableInNamingContext name ctx) = concat ["missing variable in naming context: variable: ", show name, ", NamingContext: ", show ctx]
  show (MissingTypeVariableInNamingContext name ctx) = concat ["missing type variable in naming context: type variable: ", show name, ", NamingContext: ", show ctx]
data Errors = 
    UnNameError UnNameError
  | TypingError TypingError
  | RestoreNameError RestoreNameError
  deriving (Eq)
instance Show Errors where
  show (UnNameError e) = "UnName Error: " ++ show e
  show (TypingError e) = "Typing Error: " ++ show e
  show (RestoreNameError e) = "RestoreName Error: " ++ show e


type family Named (a :: Bool) where
  Named 'True  = SString
  Named 'False = DeBrujinIndex
type NameLessVariable = Named 'False

type family Not (a :: Bool) where
  Not 'True = 'False
  Not 'False = 'True

class NameLess (f :: Bool -> *) where
  nameless :: f a -> Eff ["findVarTerm" >: ReaderEff (NamingContext -> Named a -> Maybe (Named (Not a))), "findVarType" >: ReaderEff (NamingContext -> Named a -> Maybe (Named (Not a))), ReaderDef NamingContext, EitherDef (NamingContextError a)] (f (Not a))
type UnNameError = NamingContextError 'True
unName :: NameLess f => f 'True -> Eff '[ReaderDef NamingContext, EitherDef UnNameError] (f 'False)
unName ty = runReaderEff @"findVarType" (runReaderEff @"findVarTerm" (nameless ty) findvarterm) findvartype
  where
    findvarterm ctx x = V.findIndex isBound ctx
      where
        isBound (x', VariableTermBind) | x == x' = True
        isBound _ = False
    findvartype ctx x = V.findIndex isBound ctx
      where
        isBound (x', VariableTypeBind) | x == x' = True
        isBound _ = False
type RestoreNameError = NamingContextError 'False
restoreName :: NameLess f => f 'False -> Eff '[ReaderDef NamingContext, EitherDef RestoreNameError] (f 'True)
restoreName ty = runReaderEff @"findVarType" (runReaderEff @"findVarTerm" (nameless ty) findvar) findvar
  where
    findvar ctx x = fst <$> ctx V.!? x

leaveUnName :: NameLess f => NamingContext -> f 'True -> Either UnNameError (f 'False)
leaveUnName ctx t = leaveEff . runEitherDef $ runReaderDef (unName t) ctx
leaveRestoreName :: NameLess f => NamingContext -> f 'False -> Either RestoreNameError (f 'True)
leaveRestoreName ctx t = leaveEff . runEitherDef $ runReaderDef (restoreName t) ctx
leaveUnRestoreName :: NameLess f => NamingContext -> f 'True -> Either Errors (f 'True)
leaveUnRestoreName ctx t = do
  t' <- mapLeft UnNameError $ leaveUnName ctx t
  mapLeft RestoreNameError $ leaveRestoreName ctx t'

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
leaveBetaReduction :: (NameLess f, NameLess g, IndexShift f, IndexShift g, Substitution f g) => NamingContext -> g 'True -> f 'True -> Either Errors (f 'True)
leaveBetaReduction ctx s t = do
  s1 <- mapLeft UnNameError $ leaveUnName ctx s
  t1 <- mapLeft UnNameError $ leaveUnName ctx t
  let t' = betaReduction s1 t1
  mapLeft RestoreNameError $ leaveRestoreName ctx t'



data Type a = 
    PrimitiveType SString
  | NatType
  | VariableType (Named a)
  | ArrowType (Record '["domain" :> Type a, "codomain" :> Type a])
  | RecordType (Map.Map SString (Type a))
  | AllType (Record '["name" :> SString, "body" :> Type a])
  | ExistType (Record '["name" :> SString, "body" :> Type a])
deriving instance (Eq (Type a), Eq (Named a)) => Eq (Type a)
instance (Show (Named a), Show (Type a)) => Show (Type a) where
  show (PrimitiveType ty) = show ty
  show (NatType) = "Nat"
  show (VariableType ty)  = show ty
  show (ArrowType ty)     = concat ["(", show (ty ^. #domain), " -> ", show (ty ^. #codomain), ")"]
  show (RecordType ty) = concat ["{", Map.foldrWithKey (\field ty' acc -> concat [show field, ": ", show ty', ", ", acc]) "" ty, "}"]
  show (AllType ty) = concat ["(∀", show (ty ^. #name), ".", show (ty ^. #body), ")"]
  show (ExistType ty) = concat ["(∃", show (ty ^. #name), ".", show (ty ^. #body), ")"]
type NamedType = Type 'True
type UnNamedType = Type 'False


instance NameLess Type where
  nameless (PrimitiveType ty) = return $ PrimitiveType ty
  nameless NatType = return NatType
  nameless (VariableType x) = do
    ctx <- ask
    findvar <- askEff #findVarType
    case findvar ctx x of
      Just x' -> return $ VariableType x'
      Nothing -> throwError $ MissingTypeVariableInNamingContext x ctx
  nameless (ArrowType ty) = do
    domain <- nameless $ ty ^. #domain
    codomain <- nameless $ ty ^. #codomain
    return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
  nameless (RecordType ty) = RecordType <$> mapM nameless ty
  nameless (AllType ty) = do
    let x  = ty ^. #name
    body <- local (V.cons (x, VariableTypeBind)) $ nameless (ty ^. #body)
    return . AllType $ #name @= x <: #body @= body <: nil
  nameless (ExistType ty) = do
    let x  = ty ^. #name
    body <- local (V.cons (x, VariableTypeBind)) $ nameless (ty ^. #body)
    return . ExistType $ #name @= x <: #body @= body <: nil
instance IndexOperation Type where
  indexMap _ ty@(PrimitiveType _) = return ty
  indexMap _ NatType = return NatType
  indexMap c (VariableType x) = asksEff #onvar (\onvar -> onvar c x)
  indexMap c (ArrowType ty) = do
    domain <- indexMap c $ ty ^. #domain
    codomain <- indexMap c $ ty ^. #codomain
    return . ArrowType $ ty & #domain .~ domain & #codomain .~ codomain
  indexMap c (RecordType ty) = RecordType <$> mapM (indexMap c) ty
  indexMap c (AllType ty)   = do 
    body <- indexMap (c+1) $ ty ^. #body
    return . AllType $ ty & #body .~ body
  indexMap c (ExistType ty)   = do 
    body <- indexMap (c+1) $ ty ^. #body
    return . ExistType $ ty & #body .~ body
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
  | Zero
  | Succ (Term a)
  | VariableTerm (Named a)
  | AbstractionTerm (Record '["name" :> SString, "type" :> Type a, "body" :> Term a])
  | ApplicationTerm (Record '["function" :> Term a, "argument" :> Term a])
  | RecordTerm (Map.Map SString (Term a))
  | ProjectionTerm (Record '["term" :> Term a, "label" :> SString])
  | TypeAbstractionTerm (Record '["name" :> SString, "body" :> Term a])
  | TypeApplicationTerm (Record '["term" :> Term a, "type" :> Type a])
  | PackageTerm (Record '["type" :> Type a, "term" :> Term a, "exist" :> Type a])
  | UnPackageTerm (Record '["type" :> SString, "name" :> SString, "body" :> Term a, "in" :> Term a])
deriving instance (Eq (Term a), Eq (Type a), Eq (Named a)) => Eq (Term a)
instance (Show (Named a), Show (Type a), Show (Term a)) => Show (Term a) where
  show (ConstTerm s) = show s
  show (Zero) = "0"
  show (Succ t) = concat ["succ(", show t, ")"]
  show (VariableTerm t) = show t
  show (AbstractionTerm t) = concat ["λ", show (t ^. #name), ":", show (t ^. #type), ".", show (t ^. #body)]
  show (ApplicationTerm t) = concat ["(", show (t ^. #function), " ", show (t ^. #argument), ")"]
  show (RecordTerm fields) = concat ["{", Map.foldrWithKey (\field t' acc -> concat [show field, ": ", show t', ", ", acc]) "" fields, "}"]
  show (ProjectionTerm t) = concat [show (t ^. #term), ".", show (t ^. #label)]
  show (TypeAbstractionTerm t) = concat ["λ", show (t ^. #name), ".", show (t ^. #body)]
  show (TypeApplicationTerm t) = concat [show (t ^. #term), " [", show (t ^. #type) ,"]"]
  show (PackageTerm t) = concat ["{*", show (t ^. #type), ", ", show (t ^. #term), " as ", show (t ^. #exist)]
  show (UnPackageTerm t) = concat ["let {", show (t ^. #name), ", ", show (t ^. #type), "} = ", show (t ^. #body), " in ", show (t ^. #in)]
type NamedTerm = Term 'True
type UnNamedTerm = Term 'False


instance NameLess Term where
  nameless (ConstTerm s) = return $ ConstTerm s
  nameless Zero = return Zero
  nameless (Succ t) = Succ <$> nameless t
  nameless (VariableTerm x) = do
    ctx <- ask
    findvar <- askEff #findVarTerm
    case findvar ctx x of
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
  nameless (RecordTerm fields) = RecordTerm <$> mapM nameless fields
  nameless (ProjectionTerm t) = do
    term <- nameless $ t ^. #term
    return . ProjectionTerm $ #term @= term <: #label @= t ^. #label <: nil
  nameless (TypeAbstractionTerm t) = do
    body <- local (V.cons (t ^. #name, VariableTypeBind)) $ nameless (t ^. #body)
    return . TypeAbstractionTerm $ #name @= t ^. #name <: #body @= body <: nil
  nameless (TypeApplicationTerm t) = do
    term <- nameless $ t ^. #term
    ty   <- nameless $ t ^. #type
    return . TypeApplicationTerm $ #term @= term <: #type @= ty <: nil
  nameless (PackageTerm t) = do
    ty <- nameless $ t ^. #type
    term <- nameless $ t ^. #term
    exist <- nameless $ t ^. #exist
    return . PackageTerm $ #type @= ty <: #term @= term <: #exist @= exist <: nil
  nameless (UnPackageTerm t) = do
    body <- nameless $ t ^. #body
    t' <- local (V.cons (t ^. #name, VariableTermBind) . V.cons (t ^. #type, VariableTypeBind)) $ nameless (t ^. #in)
    return . UnPackageTerm $ #type @= t ^. #type <: #name @= t ^. #name <: #body @= body <: #in @= t' <: nil
instance IndexOperation Term where
  indexMap _ t@(ConstTerm _) = return t
  indexMap _ Zero = return Zero
  indexMap c (Succ t) = Succ <$> indexMap c t
  indexMap c (VariableTerm t) = asksEff #onvar (\onvar -> onvar c t)
  indexMap c (AbstractionTerm t) = do
    ty <- asksEff #ontype (\ontype -> ontype c $ t ^. #type)
    body <- indexMap (c+1) $ t ^. #body
    return . AbstractionTerm $ t & #type .~ ty & #body .~ body
  indexMap c (ApplicationTerm t) = do
    f <- indexMap c $ t ^. #function
    arg <- indexMap c $ t ^. #argument
    return . ApplicationTerm $ t & #function .~ f & #argument .~ arg
  indexMap c (RecordTerm fields) = RecordTerm <$> mapM (indexMap c) fields
  indexMap c (ProjectionTerm t) = do
    term <- indexMap c $ t ^. #term
    return . ProjectionTerm $ t & #term .~ term
  indexMap c (TypeAbstractionTerm t) = do
    body <- indexMap (c+1) $ t ^. #body
    return . TypeAbstractionTerm $ t & #body .~ body
  indexMap c (TypeApplicationTerm t) = do
    term <- indexMap c $ t ^. #term
    ty <- asksEff #ontype (\ontype -> ontype c $ t ^. #type)
    return . TypeApplicationTerm $ t & #term .~ term & #type .~ ty
  indexMap c (PackageTerm t) = do
    ty <- asksEff #ontype (\ontype -> ontype c $ t ^. #type)
    term <- indexMap c $ t ^. #term
    exist <- asksEff #ontype (\ontype -> ontype c $ t ^. #exist)
    return . PackageTerm $ t & #type .~ ty & #term .~ term & #exist .~ exist
  indexMap c (UnPackageTerm t) = do
    body <- indexMap c $ t ^. #body
    t' <- indexMap (c+2) $ t ^. #in
    return . UnPackageTerm $ t & #body .~ body & #in .~ t'
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
isVal Zero = True
isVal (Succ _) = True
isVal (AbstractionTerm _) = True
isVal (RecordTerm _) = True
isVal (TypeAbstractionTerm _) = True
isVal (PackageTerm _) = True
isVal _ = False

eval1 :: UnNamedTerm -> Maybe UnNamedTerm
eval1 (Succ t) = Succ <$> eval1 t
eval1 (ApplicationTerm t) = case t ^. #function of
  (AbstractionTerm t') | isVal (t ^. #argument) -> Just $ betaReduction (t ^. #argument) (t' ^. #body)
  v1 | isVal v1 -> (\t2' -> ApplicationTerm $ t & #argument .~ t2') <$> eval1 (t ^. #argument)
  t1 -> (\t1' -> ApplicationTerm $ t & #function .~ t1') <$> eval1 t1
eval1 (RecordTerm fields) = RecordTerm <$> evalFields fields
  where
    evalFields = (either (const Nothing) Just) . (Map.foldrWithKey evalField (Left Map.empty))
    evalField key term (Left acc) = case eval1 term of
      Just term' -> Right $ Map.insert key term' acc
      Nothing -> Left $ Map.insert key term acc
    evalField key term (Right acc) = Right $ Map.insert key term acc
eval1 (ProjectionTerm t) = case t ^. #term of
  RecordTerm fields -> fields Map.!? (t ^. #label)
  t' -> (\term -> ProjectionTerm $ t & #term .~ term) <$> eval1 t'
eval1 (TypeApplicationTerm t) = case t ^. #term of
  (TypeAbstractionTerm t') -> Just $ betaReduction (t ^. #type) (t' ^. #body)
  t1 -> (\t1' -> TypeApplicationTerm $ t & #term .~ t1') <$> eval1 t1
eval1 (UnPackageTerm t) = case t ^. #body of
  (PackageTerm t') | isVal (t' ^. #term) -> Just $ betaReduction (t' ^. #type) (betaReduction (indexShift 1 (t' ^. #term)) (t ^. #in))
  t1 -> (\t1' -> UnPackageTerm $ t & #body .~ t1') <$> eval1 t1
eval1 (PackageTerm t) = (\t2' -> PackageTerm $ t & #term .~ t2') <$> eval1 (t ^. #term)
eval1 _ = Nothing

eval :: UnNamedTerm -> UnNamedTerm
eval t = case eval1 t of
  Just t' -> eval t'
  Nothing -> t

leaveEval :: NamingContext -> NamedTerm -> Either Errors NamedTerm
leaveEval ctx t = mapLeft UnNameError (leaveUnName ctx t) >>= mapLeft RestoreNameError . leaveRestoreName ctx . eval


type TypingContext = Vector (SString, TypedBinding)
typingContextToNamingContext :: TypingContext -> NamingContext
typingContextToNamingContext = fmap (& _2 %~ f)
  where
    f (TypedConstTermBind _) = ConstTermBind
    f (TypedVariableTermBind _) = VariableTermBind
    f TypedConstTypeBind = ConstTypeBind
    f TypedVariableTypeBind = VariableTypeBind
data TypedBinding = 
    TypedConstTermBind UnNamedType 
  | TypedVariableTermBind UnNamedType 
  | TypedConstTypeBind 
  | TypedVariableTypeBind 
  deriving (Show, Eq)
data TypingError = 
    MissingDeclarationInNamingContext SString TypingContext
  | MissingVariableTypeInNamingContext DeBrujinIndex TypingContext
  | NotMatchedTypeNatType NamedTerm NamedType
  | NotMatchedTypeArrowType NamedTerm NamedType NamedTerm NamedType 
  -- | NotMatchedTypeArrowType
  | NotMatchedTypeProjectionNotRecord
  | NotMatchedTypeProjectionLabelMissing
  | NotMatchedTypeAllType
  | NotMatchedTypeExistType NamedTerm NamedType
  | NotMatchedTypeExistTypeInstantiate
  | RestoreNameErrorWhileTypingError RestoreNameError
  deriving (Eq)
instance Show TypingError where
  show (MissingDeclarationInNamingContext name ctx) = concat ["missing constant declaration in naming context: constant: ", show name, ", NamingContext: ", show ctx]
  show (MissingVariableTypeInNamingContext name ctx) = concat ["missing variable in naming context: variable: ", show name, ", NamingContext: ", show ctx]
  show (NotMatchedTypeNatType t ty) = concat ["failed to apply succ: t = ", show t, ": ", show ty]
  show (NotMatchedTypeArrowType t1 ty1 t2 ty2) = concat ["failed to apply: t1 = ", show t1, ": ", show ty1, ", t2 = ", show t2, ": ", show ty2]
  -- show (NotMatchedTypeArrowType) = "NotMatchedTypeArrowType"
  show (NotMatchedTypeProjectionNotRecord) = "NotMatchedTypeProjectionNotRecord"
  show (NotMatchedTypeProjectionLabelMissing) = "NotMatchedTypeProjectionLabelMissing"
  show (NotMatchedTypeAllType) = "NotMatchedTypeAllType"
  show (NotMatchedTypeExistType term ty) = concat ["Expected type: ExistType, Actual type: ", show ty, ", term = ", show term]
  show (NotMatchedTypeExistTypeInstantiate) = "NotMatchedTypeExistTypeInstantiate"
  show (RestoreNameErrorWhileTypingError e) = "RestorName Error While Typing Error: " ++ show e

typing :: UnNamedTerm -> Eff '[ReaderDef TypingContext, EitherDef TypingError] UnNamedType
typing (ConstTerm s) = do
  bind <- asks $ fmap (^. _2) . V.find ((==) s . (^. _1))
  case bind of
    Just (TypedConstTermBind ty) -> return ty
    _ -> ask >>= throwError . MissingDeclarationInNamingContext s
typing Zero = return NatType
typing (Succ t) = do
  ty <- typing t
  case ty of
    NatType -> return NatType
    _ -> do
      ctx <- asks typingContextToNamingContext
      t' <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName t) ctx
      ty' <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName ty) ctx
      throwError $ NotMatchedTypeNatType t' ty'
typing (VariableTerm t) = do
  ctx <- ask
  case ctx V.!? t of
    Just (_, TypedVariableTermBind ty) -> return $ indexShift (t+1) ty
    _ -> throwError $ MissingVariableTypeInNamingContext t ctx
typing (AbstractionTerm t) = do
  codomain <- local (V.cons (t ^. #name, TypedVariableTermBind (t ^. #type))) $ typing (t ^. #body)
  return . ArrowType $ #domain @= t ^. #type <: #codomain @= indexShift (-1) codomain <: nil
typing (ApplicationTerm t) = do
  ty1 <- typing $ t ^. #function
  ty2 <- typing $ t ^. #argument
  case ty1 of
    ArrowType t' | t' ^. #domain == ty2 -> return $ t' ^. #codomain
    _ -> do
      ctx <- asks typingContextToNamingContext
      t1'  <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName $ t ^. #function) ctx
      ty1' <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName ty1) ctx
      t2'  <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName $ t ^. #argument) ctx
      ty2' <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName ty2) ctx
      throwError $ NotMatchedTypeArrowType t1' ty1' t2' ty2'
typing (RecordTerm fields) = RecordType <$> mapM typing fields
typing (ProjectionTerm t) = do
  ty <- typing $ t ^. #term
  case ty of
    RecordType fields -> case fields Map.!? (t ^. #label) of
      Just ty' -> return ty'
      Nothing -> throwError NotMatchedTypeProjectionLabelMissing
    _ -> throwError NotMatchedTypeProjectionNotRecord
typing (TypeAbstractionTerm t) = do
  body <- local (V.cons (t ^. #name, TypedVariableTypeBind)) $ typing (t ^. #body)
  return . AllType $ #name @= t ^. #name <: #body @= body <: nil
typing (TypeApplicationTerm t) = do
  term <- typing $ t ^. #term
  case term of
    AllType t' -> return $ betaReduction (t ^. #type) (t' ^. #body)
    _ -> throwError NotMatchedTypeAllType
typing (PackageTerm t) = do
  case t ^. #exist of
    ExistType ty -> do
      term <- typing $ t ^. #term
      if term == betaReduction (t ^. #type) (ty ^. #body)
        then return $ t ^. #exist
        else throwError NotMatchedTypeExistTypeInstantiate
    ty -> do
      ctx <- asks typingContextToNamingContext
      ty' <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName ty) ctx
      t' <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName (PackageTerm t)) ctx
      throwError $ NotMatchedTypeExistType t' ty'
typing (UnPackageTerm t) = do
  body <- typing $ t ^. #body
  case body of
    ExistType ty -> indexShift (-2) <$> local (V.cons (t ^. #name, TypedVariableTermBind (ty ^. #body)) . V.cons (t ^. #type, TypedVariableTypeBind)) (typing (t ^. #in))
    ty -> do
      ctx <- asks typingContextToNamingContext
      ty' <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName ty) ctx
      t' <- castEff . mapLeftDef RestoreNameErrorWhileTypingError $ runReaderDef (restoreName (UnPackageTerm t)) ctx
      throwError $ NotMatchedTypeExistType t' ty'

leaveTyping :: TypingContext -> NamedTerm -> Either Errors NamedType
leaveTyping ctx t = do
  let ctx' = typingContextToNamingContext ctx
  t1 <- mapLeft UnNameError $ leaveUnName ctx' t
  t' <- mapLeft TypingError . leaveEff . runEitherDef $ runReaderDef (typing t1) ctx
  mapLeft RestoreNameError $ leaveRestoreName ctx' t'
