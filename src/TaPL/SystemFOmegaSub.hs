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
import qualified RIO.Map as Map
import qualified RIO.Vector as V

import Control.Lens hiding ((:>), (^.), Context)
import Control.Monad.Error.Class
import Data.Extensible hiding (record)
import Data.Extensible.Effect.Default

import TaPL.NameLess

import SString
import MapLeftEff
-- import qualified Debug.Trace as D



data Errors = 
    NameLessError (NameLessErrors TypedBinding)
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
leaveBetaReduction :: (NameLess f 'True b, NameLess f 'False b, NameLess g 'True b, IndexShift f, IndexShift g, Substitution f g) => Context b -> g 'True -> f 'True -> Either (NameLessErrors b) (f 'True)
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

data Variance = Invariant | Convariant deriving (Eq)
instance Show Variance where
  show Invariant = "#"
  show Convariant = ""

data Type a =
    TopType
  | UnitType
  | NatType
  -- | BoolType
  | PrimitiveType SString
  | VariableType (Named a) 
  | ArrowType (Record '["domain" :> Type a, "codomain" :> Type a])
  | RecordType (Map.Map SString (Variance, Type a))
  | UniversalType (Record '["name" :> SString, "bound" :> Type a , "body" :> Type a])
  | ExistentialType (Record '["name" :> SString, "bound" :> Type a, "body" :> Type a])
  | AbstractionType (Record '["name" :> SString, "kind" :> Kind, "body" :> Type a])
  | ApplicationType (Record '["function" :> Type a, "argument" :> Type a])
deriving instance (Eq (Named a), Eq (Type a)) => Eq (Type a)
instance (Show (Named a), Show (Type a)) => Show (Type a) where
  show TopType = "T"
  show UnitType = "()"
  show NatType = "Nat"
  -- show BoolType = "Bool"
  show (PrimitiveType s) = show s
  show (VariableType ty)  = show ty
  show (ArrowType ty)     = concat ["(", show (ty ^. #domain), " -> ", show (ty ^. #codomain), ")"]
  show (RecordType fields) = concat ["{", Map.foldrWithKey (\field (v, ty) acc -> concat [show v, show field, ": ", show ty, ", ", acc]) "" fields, "}"]
  show (UniversalType ty) = concat ["(∀", show (ty ^. #name), "<:", show (ty ^. #bound) ,".", show (ty ^. #body), ")"]
  show (ExistentialType ty) = concat ["(∃", show (ty ^. #name), "<:", show (ty ^. #bound), ".", show (ty ^. #body), ")"]
  show (AbstractionType ty) = concat ["λ", show (ty ^. #name), "::", show (ty ^. #kind), ".", show (ty ^. #body)]
  show (ApplicationType ty) = concat ["(", show (ty ^. #function), " ", show (ty ^. #argument), ")"]
type NamedType = Type 'True
type UnNamedType = Type 'False

data TypedBinding = 
    ConstTermBind UnNamedType
  | VariableTermBind UnNamedType 
  | ConstTypeBind 
  | VariableTypeBind UnNamedType
  deriving (Show, Eq)
instance Binding Type TypedBinding where
  binding _ = VariableTypeBind undefined
instance Binding Term TypedBinding where
  binding _ = VariableTermBind undefined
instance FindVar Type 'True TypedBinding where
  findvar _ ctx x = V.findIndex isBound ctx
    where
      isBound (x', VariableTypeBind _) | x == x' = True
      isBound _ = False
instance FindVar Type 'False TypedBinding where
  findvar _ ctx x = fst <$> ctx V.!? x
instance (FindVar Type a b, Binding Type b) => NameLess Type a b where
  nameless TopType = return TopType
  nameless UnitType = return UnitType
  nameless NatType = return NatType
  -- nameless BoolType = return BoolType
  nameless (PrimitiveType s) = return $ PrimitiveType s
  nameless (VariableType x) = do
    ctx <- ask
    case findvar (Proxy :: Proxy Type) ctx x of
      Just x' -> return $ VariableType x'
      Nothing -> throwError $ MissingVariableInContext x ctx
  nameless (ArrowType ty) = do
    domain <- nameless $ ty ^. #domain
    codomain <- nameless $ ty ^. #codomain
    return . ArrowType $ #domain @= domain <: #codomain @= codomain <: nil
  nameless (RecordType fields) = RecordType <$> mapM (traverse nameless) fields
  nameless (UniversalType ty) = do
    let x  = ty ^. #name
    bound <- nameless $ ty ^. #bound
    -- body <- local (V.cons (x, VariableTypeBind undefined)) $ nameless (ty ^. #body)
    body <- local (V.cons (x, binding (Proxy :: Proxy Type))) $ nameless (ty ^. #body)
    return . UniversalType $ #name @= x <: #bound @= bound <: #body @= body <: nil
  nameless (ExistentialType ty) = do
    let x  = ty ^. #name
    bound <- nameless $ ty ^. #bound
    -- body <- local (V.cons (x, VariableTypeBind undefined)) $ nameless (ty ^. #body)
    body <- local (V.cons (x, binding (Proxy :: Proxy Type))) $ nameless (ty ^. #body)
    return . ExistentialType $ #name @= x <: #bound @= bound <: #body @= body <: nil
  nameless (AbstractionType ty) = do
    let x = ty ^. #name
    body <- local (V.cons (x, binding (Proxy :: Proxy Type))) $ nameless (ty ^. #body)
    return . AbstractionType $ #name @= x <: #kind @= ty ^. #kind <: #body @= body <: nil
  nameless (ApplicationType ty) = do
    t1 <- nameless $ ty ^. #function
    t2 <- nameless $ ty ^. #argument
    return . ApplicationType $ #function @= t1 <: #argument @= t2 <: nil
instance IndexOperation Type where
  indexMap _ TopType = return TopType
  indexMap _ UnitType = return UnitType
  indexMap _ NatType = return NatType
  -- indexMap _ BoolType = return BoolType
  indexMap _ ty@(PrimitiveType _) = return ty
  indexMap c (VariableType x) = asksEff #onvar (\onvar -> onvar c x)
  indexMap c (ArrowType ty) = do
    domain <- indexMap c $ ty ^. #domain
    codomain <- indexMap c $ ty ^. #codomain
    return . ArrowType $ ty & #domain .~ domain & #codomain .~ codomain
  indexMap c (RecordType ty) = RecordType <$> mapM (traverse (indexMap c)) ty
  indexMap c (UniversalType ty) = do 
    bound <- indexMap c $ ty ^. #bound
    body <- indexMap (c+1) $ ty ^. #body
    return . UniversalType $ ty & #bound .~ bound & #body .~ body
  indexMap c (ExistentialType ty) = do 
    bound <- indexMap c $ ty ^. #bound
    body <- indexMap (c+1) $ ty ^. #body
    return . ExistentialType $ ty & #bound .~ bound & #body .~ body
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
    Unit
  | Zero
  | Succ (Term a)
  -- | TRUE
  -- | FALSE
  -- | IF (Record '["cond" :> Term a, "then" :> Term a, "else" :> Term a])
  | ConstTerm SString
  | VariableTerm (Named a)
  | AbstractionTerm (Record '["name" :> SString, "type" :> Type a, "body" :> Term a])
  | ApplicationTerm (Record '["function" :> Term a, "argument" :> Term a])
  | RecordTerm (Map.Map SString (Variance, Term a))
  | ProjectionTerm (Record '["term" :> Term a, "label" :> SString])
  | UpdateTerm (Record '["record" :> Term a, "label" :> SString, "new" :> Term a])
  | TypeAbstractionTerm (Record '["name" :> SString, "bound" :> Type a, "body" :> Term a])
  | TypeApplicationTerm (Record '["term" :> Term a, "type" :> Type a])
  | PackageTerm (Record '["type" :> Type a, "term" :> Term a, "exist" :> Type a])
  | UnPackageTerm (Record '["type" :> SString, "name" :> SString, "body" :> Term a, "in" :> Term a])
deriving instance (Eq (Term a), Eq (Type a), Eq (Named a)) => Eq (Term a)
instance (Show (Named a), Show (Type a), Show (Term a)) => Show (Term a) where
  show Unit = "()"
  show Zero = "0"
  show (Succ t) = concat ["succ(", show t, ")"]
  -- show TRUE = "True"
  -- show FALSE = "False"
  -- show (IF t) = concat ["if ", show (t ^. #cond), " then ", show (t ^. #then), " else ", show (t ^. #else)]
  show (ConstTerm s) = show s
  show (VariableTerm t) = show t
  show (AbstractionTerm t) = concat ["λ", show (t ^. #name), ":", show (t ^. #type), ".", show (t ^. #body)]
  show (ApplicationTerm t) = concat ["(", show (t ^. #function), " ", show (t ^. #argument), ")"]
  show (RecordTerm fields) = concat ["{", Map.foldrWithKey (\field (v, t) acc -> concat [show v, show field, ": ", show t, ", ", acc]) "" fields, "}" ]
  show (ProjectionTerm t) = concat [show (t ^. #term), ".", show (t ^. #label)]
  show (UpdateTerm t) = concat [show (t ^. #record), " <- ", show (t ^. #label), " = ", show (t ^. #new)]
  show (TypeAbstractionTerm t) = concat ["λ", show (t ^. #name), "<:", show (t ^. #bound), ".", show (t ^. #body)]
  show (TypeApplicationTerm t) = concat [show (t ^. #term), " [", show (t ^. #type) ,"]"]
  show (PackageTerm t) = concat ["{*", show (t ^. #type), ", ", show (t ^. #term), " as ", show (t ^. #exist)]
  show (UnPackageTerm t) = concat ["let {", show (t ^. #name), ", ", show (t ^. #type), "} = ", show (t ^. #body), " in ", show (t ^. #in)]
type NamedTerm = Term 'True
type UnNamedTerm = Term 'False

instance FindVar Term 'True TypedBinding where
  findvar _ ctx x = V.findIndex isBound ctx
    where
      isBound (x', VariableTermBind _) | x == x' = True
      isBound _ = False
instance FindVar Term 'False TypedBinding where
  findvar _ ctx x = fst <$> ctx V.!? x
instance (FindVar Term a b, FindVar Type a b, Binding Term b, Binding Type b) => NameLess Term a b where
  nameless Unit = return Unit
  nameless Zero = return Zero
  nameless (Succ t) = Succ <$> nameless t
  -- nameless TRUE = return TRUE
  -- nameless FALSE = return FALSE
  -- nameless (IF t) = do
  --   t1 <- nameless $ t ^. #cond
  --   t2 <- nameless $ t ^. #then
  --   t3 <- nameless $ t ^. #else
  --   return . IF $ #cond @= t1 <: #then @= t2 <: #else @= t3 <: nil
  nameless (ConstTerm s) = return $ ConstTerm s
  nameless (VariableTerm x) = do
    ctx <- ask
    case findvar (Proxy :: Proxy Term) ctx x of
      Just x'  -> return $ VariableTerm x'
      Nothing -> throwError $ MissingVariableInContext x ctx
  nameless (AbstractionTerm t) = do
    let x  = t ^. #name
    ty <- nameless $ t ^. #type
    body <- local (V.cons (x, binding (Proxy :: Proxy Term))) $ nameless (t ^. #body)
    return . AbstractionTerm $ #name @= x <: #type @= ty <: #body @= body <: nil
  nameless (ApplicationTerm t) = do
    t1 <- nameless $ t ^. #function
    t2 <- nameless $ t ^. #argument
    return . ApplicationTerm $ #function @= t1 <: #argument @= t2 <: nil
  nameless (RecordTerm fields) = RecordTerm <$> mapM (traverse nameless) fields
  nameless (ProjectionTerm t) = do
    term <- nameless $ t ^. #term
    return . ProjectionTerm $ #term @= term <: #label @= t ^. #label <: nil
  nameless (UpdateTerm t) = do
    record <- nameless $ t ^. #record
    new <- nameless $ t ^. #new
    return . UpdateTerm $ #record @= record <: #label @= t ^. #label <: #new @= new <: nil
  nameless (TypeAbstractionTerm t) = do
    bound <- nameless $ t ^. #bound
    body <- local (V.cons (t ^. #name, binding (Proxy :: Proxy Type))) $ nameless (t ^. #body)
    return . TypeAbstractionTerm $ #name @= t ^. #name <: #bound @= bound <: #body @= body <: nil
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
    t' <- local (V.cons (t ^. #name, binding (Proxy :: Proxy Term)) . V.cons (t ^. #type, binding (Proxy :: Proxy Type))) $ nameless (t ^. #in)
    return . UnPackageTerm $ #type @= t ^. #type <: #name @= t ^. #name <: #body @= body <: #in @= t' <: nil
instance IndexOperation Term where
  indexMap _ t@Unit = return t
  indexMap _ t@Zero = return t
  indexMap c (Succ t) = Succ <$> indexMap c t
  -- indexMap _ t@TRUE = return t
  -- indexMap _ t@FALSE = return t
  -- indexMap c (IF t) = do
  --   t1 <- indexMap c $ t ^. #cond
  --   t2 <- indexMap c $ t ^. #then
  --   t3 <- indexMap c $ t ^. #else
  --   return . IF $ t & #cond .~ t1 & #then .~ t2 & #else .~ t3
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
  indexMap c (RecordTerm fields) = RecordTerm <$> mapM (traverse (indexMap c)) fields
  indexMap c (ProjectionTerm t) = do
    term <- indexMap c $ t ^. #term
    return . ProjectionTerm $ t & #term .~ term
  indexMap c (UpdateTerm t) = do
    record <- indexMap c $ t ^. #record
    new <- indexMap c $ t ^. #new
    return . UpdateTerm $ t & #record .~ record & #new .~ new
  indexMap c (TypeAbstractionTerm t) = do
    bound <- asksEff #ontype (\ontype -> ontype c $ t ^. #bound)
    body <- indexMap (c+1) $ t ^. #body
    return . TypeAbstractionTerm $ t & #bound .~ bound & #body .~ body
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
isVal Unit = True
isVal Zero = True
isVal t | isNum t = True
  where
    isNum Zero = True
    isNum (Succ t') = isNum t'
    isNum _ = False
-- isVal TRUE = True
-- isVal FALSE = True
isVal (ConstTerm _) = True
isVal (AbstractionTerm _) = True
isVal (RecordTerm fields) = all (isVal . snd) fields
isVal (TypeAbstractionTerm _) = True
isVal (PackageTerm _) = True
isVal _ = False

eval1 :: UnNamedTerm -> Maybe UnNamedTerm
eval1 (Succ t) = Succ <$> eval1 t
-- eval1 (IF t) 
--   | t ^. #cond == TRUE = return $ t ^. #then
--   | t ^. #cond == FALSE = return $ t ^. #else
--   | otherwise = (\cond -> IF $ t & #cond .~ cond) <$> eval (t ^. #cond)
eval1 (ApplicationTerm t) = case t ^. #function of
  (AbstractionTerm t') | isVal (t ^. #argument) -> Just $ betaReduction (t ^. #argument) (t' ^. #body)
  v1 | isVal v1 -> (\t2' -> ApplicationTerm $ t & #argument .~ t2') <$> eval1 (t ^. #argument)
  t1 -> (\t1' -> ApplicationTerm $ t & #function .~ t1') <$> eval1 t1
eval1 (RecordTerm fields) = RecordTerm <$> evalFields fields
  where
    evalFields = (either (const Nothing) Just) . (Map.foldrWithKey evalField (Left Map.empty))
    evalField key (v, term) (Left acc) = case eval1 term of
      Just term' -> Right $ Map.insert key (v, term') acc
      Nothing -> Left $ Map.insert key (v, term) acc
    evalField key (v, term) (Right acc) = Right $ Map.insert key (v, term) acc
eval1 (ProjectionTerm t) = case t ^. #term of
  RecordTerm fields -> snd <$> fields Map.!? (t ^. #label)
  t' -> (\term -> ProjectionTerm $ t & #term .~ term) <$> eval1 t'
eval1 (UpdateTerm t) = 
  let new = t ^. #new in
  case t ^. #record of
    RecordTerm fields | all (isVal . snd) fields && isVal new -> const new <$> fields Map.!? (t ^. #label)
    v | isVal v -> (\new' -> UpdateTerm $ t & #new .~ new') <$> eval1 new
    t' -> (\t'' -> UpdateTerm $ t & #record .~ t'') <$> eval1 t'
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

-- leaveEval :: (Binding Type b, Binding Term b) => Context b -> NamedTerm -> Either (NameLessErrors b) NamedTerm
leaveEval :: TypingContext -> NamedTerm -> Either (NameLessErrors TypedBinding) NamedTerm
leaveEval ctx t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ mapLeftDef UnNameError (unName t) >>= mapLeftDef RestoreNameError . restoreName . eval

-- type TypingContext = Vector (SString, TypedBinding)
-- typingContextToNamingContext :: TypingContext -> NamingContext
-- typingContextToNamingContext = fmap (& _2 %~ f)
--   where
--     f (TypedConstTermBind _) = ConstTermBind
--     f (TypedVariableTermBind _) = VariableTermBind
--     f TypedConstTypeBind = ConstTypeBind
--     f (TypedVariableTypeBind _) = VariableTypeBind
data KindingError =
    MissingTypeVariableInNamingContextWhileKinding
  | UnMatchedKindStarKindInRecordType
  | UnMatchedKindArrowType
  | UnMatchedKindUniversalType
  | UnMatchedKindExistentialType
  | UnMatchedKindApplicationType
  deriving (Show, Eq)
kinding :: UnNamedType -> Eff '[EitherDef KindingError, ReaderDef (Context TypedBinding)] Kind
kinding TopType = return StarKind
kinding UnitType = return StarKind
kinding NatType = return StarKind
-- kinding BoolType = return StarKind
kinding (PrimitiveType _) = return StarKind
kinding (VariableType x) = do
  ctx <- ask
  case snd <$> ctx V.!? x of
    Just (VariableTypeBind ty) -> kinding ty
    _ -> throwError MissingTypeVariableInNamingContextWhileKinding
kinding (ArrowType ty) = do
  domain <- kinding $ ty ^. #domain
  codomain <- kinding $ ty ^. #codomain
  if domain == StarKind && codomain == StarKind
    then return StarKind
    else throwError UnMatchedKindArrowType
kinding (RecordType fields) = do
  mapM_ (traverse (kindcheck <=< kinding)) fields
  return StarKind
  where
    kindcheck StarKind = return StarKind
    kindcheck _ = throwError UnMatchedKindStarKindInRecordType
kinding (UniversalType ty) = do
  body <- local (V.cons (ty ^. #name, VariableTypeBind (ty ^. #bound))) $ kinding (ty ^. #body)
  if body == StarKind
    then return StarKind
    else throwError UnMatchedKindUniversalType
kinding (ExistentialType ty) = do
  body <- local (V.cons (ty ^. #name, VariableTypeBind (ty ^. #bound))) $ kinding (ty ^. #body)
  if body == StarKind
    then return StarKind
    else throwError UnMatchedKindExistentialType
kinding (AbstractionType ty) = do
  let k = ty ^. #kind
      top = topOf k
  codomain <- local (V.cons (ty ^. #name, VariableTypeBind top)) $ kinding (ty ^. #body)
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
  | UnMatchedTypeProjectionNotRecord
  | UnMatchedTypeProjectionLabelMissing
  | UnMatchedTypeUpdateNotRecord
  | UnMatchedVarianceUpdate
  | UnMatchedTypeUpdateLabelMissing
  | UnMatchedTypeUpdateNewNotSubOld
  | UnMatchedTypeUniversalType
  | UnMatchedTypeUniversalTypeSubType
  | UnMatchedTypeExistentialTypeKindIsNotStar
  | UnMatchedTypeExistentialTypeExpected
  | UnMatchedTypeExistType
  | UnMatchedTypeExistTypeNotSubtype
  | UnMatchedTypeExistTypeInstantiate
  -- | RestoreNameErrorWhileTypingError RestoreNameError
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

type TypingContext = Context TypedBinding
typing :: UnNamedTerm -> Eff '[EitherDef TypingError, ReaderDef TypingContext] UnNamedType
typing Unit = return UnitType
typing Zero = return NatType
typing (Succ t) = do
  ty <- typing t
  mapLeftDef PromotingError (ty `isSubTypeOf` NatType) >>= 
    bool
      (throwError UnMatchedTypeNatType)
      (return NatType)
typing (ConstTerm s) = do
  bind <- asks $ fmap (^. _2) . V.find ((==) s . (^. _1))
  case bind of
    Just (ConstTermBind ty) -> return ty
    _ -> throwError MissingDeclarationInNamingContext
typing (VariableTerm x) = do
  ctx <- ask
  case ctx V.!? x of
    Just (_, VariableTermBind ty) -> return $ indexShift (x+1) ty
    _ -> throwError MissingVariableTypeInNamingContext
typing (AbstractionTerm t) = do
  k <- mapLeftDef KindingError . kinding $ t ^. #type
  if k /= StarKind
    then throwError UnMatchedTypeArrowTypeKindIsNotStar
    else do
      let domain = t ^. #type
      codomain <- local (V.cons (t ^. #name, VariableTermBind domain)) $ typing (t ^. #body)
      return . ArrowType $ #domain @= domain <: #codomain @= indexShift (-1) codomain <: nil
typing (ApplicationTerm t) = do
  ty1 <- castEff . expose =<< typing (t ^. #function)
  ty2 <- typing $ t ^. #argument
  case ty1 of
    ArrowType ty1' -> do
      b <- mapLeftDef PromotingError $ ty2 `isSubTypeOf` (ty1' ^. #domain)
      if b
        then return $ ty1' ^. #codomain
        else throwError UnMatchedTypeArrowTypeSubType
    _ -> throwError UnMatchedTypeArrowType
typing (RecordTerm fields) = RecordType <$> mapM (traverse typing) fields
typing (ProjectionTerm t) = do
  ty <- castEff . expose =<< typing (t ^. #term)
  case ty of
    RecordType fields -> case fields Map.!? (t ^. #label) of
      Just (_, ty') -> return ty'
      Nothing -> throwError UnMatchedTypeProjectionLabelMissing
    _ -> throwError UnMatchedTypeProjectionNotRecord
typing (UpdateTerm t) = do
  record <- castEff . expose =<< typing (t ^. #record)
  new <- typing $ t ^. #new
  case record of
    RecordType fields -> 
      case fields Map.!? (t ^. #label) of
        Just (v, old) 
          | v /= Convariant -> throwError UnMatchedVarianceUpdate
          | otherwise ->
            mapLeftDef PromotingError (new `isSubTypeOf` old) >>= 
            bool
              (throwError UnMatchedTypeUpdateNewNotSubOld)
              (return record)
        _ -> throwError UnMatchedTypeUpdateLabelMissing
    _ -> throwError UnMatchedTypeUpdateNotRecord
typing (TypeAbstractionTerm t) = do
  let x = t ^. #name
      bound = t ^. #bound
  body <- local (V.cons (x, VariableTypeBind bound)) $ typing (t ^. #body)
  return . UniversalType $ #name @= x <: #bound @= bound <: #body @= body <: nil
typing (TypeApplicationTerm t) = do
  term <- castEff . expose =<< typing (t ^. #term)
  case term of
    UniversalType ty ->
      mapLeftDef PromotingError ((t ^. #type) `isSubTypeOf` (ty ^. #bound)) >>=
      bool
        (throwError UnMatchedTypeUniversalTypeSubType)
        (return $ betaReduction (t ^. #type) (ty ^. #body))
    _ -> throwError UnMatchedTypeUniversalType
typing (PackageTerm t) = do
  let ty = t ^. #exist
  k <- mapLeftDef KindingError $ kinding ty
  if k /= StarKind
    then throwError UnMatchedTypeExistentialTypeKindIsNotStar
    else
      case normalize ty of
        ExistentialType ty' ->
          mapLeftDef PromotingError ((t ^. #type) `isSubTypeOf` (ty' ^. #bound)) >>=
          bool
            (throwError UnMatchedTypeExistTypeNotSubtype)
            (do
              let concrete = betaReduction (t ^. #type) (t ^. #exist)
              term <- typing $ t ^. #term
              mapLeftDef PromotingError (term `isSubTypeOf` concrete) >>=
                bool
                  (throwError UnMatchedTypeExistTypeInstantiate)
                  (return ty))
        _ -> throwError UnMatchedTypeExistentialTypeExpected
typing (UnPackageTerm t) = do
  body <- castEff . expose =<< typing (t ^. #body)
  case body of
    ExistentialType ty -> indexShift (-2) <$> local (V.cons (t ^. #name, VariableTermBind (ty ^. #body)) . V.cons (t ^. #type, VariableTypeBind (ty ^. #bound))) (typing (t ^. #in))
    _ -> throwError UnMatchedTypeExistentialTypeExpected

leaveTyping :: TypingContext -> NamedTerm -> Either Errors NamedType
leaveTyping ctx t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ do
  t' <- mapLeftDef (NameLessError . UnNameError) $ unName t
  ty <- mapLeftDef TypingError $ typing t'
  mapLeftDef (NameLessError . RestoreNameError) $ restoreName ty
 

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
    Just (VariableTypeBind ty') -> return $ indexShift (x+1) ty'
    _ -> throwError $ MissingTypeVariableInNamingContextWhilePromoting x ctx
promoteVariable (ApplicationType ty) = (\ty' -> ApplicationType $ ty & #function .~ ty') <$> promoteVariable (ty ^. #function)
promoteVariable _ = throwError UnMatchedPromoting

-- perform betaReduction on the left of type application
normalize :: UnNamedType -> UnNamedType
normalize (ApplicationType ty) = case normalize $ ty ^. #function of
    AbstractionType ty' -> normalize $ betaReduction (ty ^. #argument) (ty' ^. #body)
    f -> ApplicationType $ ty & #function .~ f
normalize ty = ty
leaveNormalize :: TypingContext -> NamedType -> Either (NameLessErrors TypedBinding) NamedType
leaveNormalize ctx ty = leaveEff . (`runReaderDef` ctx) . runEitherDef $ mapLeftDef UnNameError (unName ty) >>= mapLeftDef RestoreNameError . restoreName . normalize

isSubTypeOf :: UnNamedType -> UnNamedType -> Eff '[EitherDef PromotingError, ReaderDef TypingContext] Bool
isSubTypeOf ty1 ty2 | ty1 `isEquivalentTo` ty2 = return True
isSubTypeOf ty1 ty2 = case (normalize ty1, normalize ty2) of
  (_, TopType) -> return True
  (ty1'@(VariableType _), ty2') -> promoteVariable ty1' >>= (`isSubTypeOf` ty2')
  (ArrowType ty1', ArrowType ty2') -> (&&) <$> ((ty1' ^. #domain) `isSubTypeOf` (ty2' ^. #domain)) <*> ((ty1' ^. #codomain) `isSubTypeOf` (ty2' ^. #codomain))
  (RecordType fields1, RecordType fields2) -> Map.foldrWithKey isSubTypeFieldOf (return True) fields2
    where
      isSubTypeFieldOf label (v2, ty2') mb = 
        case fields1 Map.!? label of
          Just (v1, ty1') | v1 == Invariant || v2 == Convariant -> 
            (&&) <$> mb <*> (ty1' `isSubTypeOf` ty2')
          _ -> return False
  (UniversalType ty1', UniversalType ty2') -> do
    let bound1 = ty1' ^. #bound
        bound2 = ty2' ^. #bound
    b1 <- (&&) <$> (bound1 `isSubTypeOf` bound2) <*> (bound2 `isSubTypeOf` bound1) -- equivalent??
    b2 <- local (V.cons (ty1' ^. #name <> "_" <> ty2' ^. #name, VariableTypeBind bound1)) $ (ty1' ^. #body) `isSubTypeOf` (ty2' ^. #body)
    return $ b1 && b2
  (ExistentialType ty1', ExistentialType ty2') -> do
    let bound1 = ty1' ^. #bound
        bound2 = ty2' ^. #bound
    b1 <- (&&) <$> (bound1 `isSubTypeOf` bound2) <*> (bound2 `isSubTypeOf` bound1) -- equivalent??
    b2 <- local (V.cons (ty1' ^. #name <> "_" <> ty2' ^. #name, VariableTypeBind bound1)) $ (ty1' ^. #body) `isSubTypeOf` (ty2' ^. #body)
    return $ b1 && b2
  (AbstractionType ty1', AbstractionType ty2') -> do
    let k = ty1' ^. #kind
    b <- local (V.cons (ty1' ^. #name <> "_" <> ty2' ^. #name, VariableTypeBind (topOf k))) $ (ty1' ^. #body) `isSubTypeOf` (ty2' ^. #body)
    return $ (k == ty2' ^. #kind) && b
  (ty1'@(ApplicationType _), ty2') -> promoteVariable ty1' >>= (`isSubTypeOf` ty2')
  _ -> return False

isEquivalentTo :: UnNamedType -> UnNamedType -> Bool
isEquivalentTo ty1 ty2 = case (normalize ty1, normalize ty2) of
  (TopType, TopType) -> True
  (UnitType, UnitType) -> True
  (NatType, NatType) -> True
  (PrimitiveType s1, PrimitiveType s2) -> s1 == s2
  (VariableType x, VariableType y) -> x == y
  (ArrowType ty1', ArrowType ty2') -> ((ty1' ^. #domain) `isEquivalentTo` (ty2' ^. #domain)) && ((ty1' ^. #codomain) `isEquivalentTo` (ty2' ^. #codomain))
  (RecordType fields1, RecordType fields2) -> zipFold (Map.toList fields1) (Map.toList fields2)
  (UniversalType ty1', UniversalType ty2') -> ((ty1' ^. #bound) `isEquivalentTo` (ty2' ^. #bound)) && ((ty1' ^. #body) `isEquivalentTo` (ty2' ^. #body))
  (ExistentialType ty1', ExistentialType ty2') -> ((ty1' ^. #bound) `isEquivalentTo` (ty2' ^. #bound)) && ((ty1' ^. #body) `isEquivalentTo` (ty2' ^. #body))
  (AbstractionType ty1', AbstractionType ty2') -> (ty1' ^. #kind == ty2' ^. #kind) && ((ty1' ^. #body) `isEquivalentTo` (ty2' ^. #body))
  (ApplicationType ty1', ApplicationType ty2') -> ((ty1' ^. #function) `isEquivalentTo` (ty2' ^. #function)) && ((ty1' ^. #argument) `isEquivalentTo` (ty2' ^. #argument))
  _ -> False
  where
    zipFold [] [] = True
    zipFold [] _ = False
    zipFold _ [] = False
    zipFold ((k1, (v1, ty1)):xs1) ((k2, (v2, ty2)):xs2) = k1 == k2 && v1 == v2 && ty1 `isEquivalentTo` ty2 && zipFold xs1 xs2

leaveIsSubTypeOf :: TypingContext -> NamedType -> NamedType -> Either Errors Bool
leaveIsSubTypeOf ctx ty1 ty2 = leaveEff . (`runReaderDef` ctx) . runEitherDef $ do
  ty1' <- mapLeftDef (NameLessError . UnNameError) $ unName ty1
  ty2' <- mapLeftDef (NameLessError . UnNameError) $ unName ty2
  mapLeftDef (TypingError . PromotingError) $ ty1' `isSubTypeOf` ty2'
