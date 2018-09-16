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
import qualified RIO.List as L
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
  s' <- mapLeftDef UnNameError $ unName s
  t' <- mapLeftDef UnNameError $ unName t
  let t1 = betaReduction s' t'
  mapLeftDef RestoreNameError $ restoreName t1



data Kind = 
    StarKind 
  | ArrowKind (Record '["domain" :> Kind, "codomain" :> Kind])
  deriving (Eq)
instance Show Kind where
  show StarKind = "*"
  show (ArrowKind k) = concat ["(", show (k ^. #domain), " -> ", show (k ^. #codomain), ")"]

data Variance = Invariant | Covariant deriving (Eq)
instance Show Variance where
  show Invariant = "#"
  show Covariant = ""

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
  show (RecordType fields) = concat ["{", L.intercalate ", " . fmap (\(label, (v, ty)) -> concat [show v, show label, ": ", show ty]) $ Map.toList fields, "}"]
  show (UniversalType ty) = concat ["(∀", show (ty ^. #name), "<:", show (ty ^. #bound) ,".", show (ty ^. #body), ")"]
  show (ExistentialType ty) = concat ["(∃", show (ty ^. #name), "<:", show (ty ^. #bound), ".", show (ty ^. #body), ")"]
  show (AbstractionType ty) = concat ["λ", show (ty ^. #name), "::", show (ty ^. #kind), ".", show (ty ^. #body)]
  show (ApplicationType ty) = concat ["(", show (ty ^. #function), " ", show (ty ^. #argument), ")"]
type NamedType = Type 'True
type UnNamedType = Type 'False

data TypedBinding = 
    ConstTermBind UnNamedType
  | VariableTermBind UnNamedType 
  | TypeAbbreviationBind UnNamedType
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
      isBound (x', TypeAbbreviationBind _) | x == x' = True
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
    let name  = ty ^. #name
    bound <- nameless $ ty ^. #bound
    body <- local (V.cons (name, binding (Proxy :: Proxy Type))) $ nameless (ty ^. #body)
    return . UniversalType $ #name @= name <: #bound @= bound <: #body @= body <: nil
  nameless (ExistentialType ty) = do
    let name = ty ^. #name
    bound <- nameless $ ty ^. #bound
    body <- local (V.cons (name, binding (Proxy :: Proxy Type))) $ nameless (ty ^. #body)
    return . ExistentialType $ #name @= name <: #bound @= bound <: #body @= body <: nil
  nameless (AbstractionType ty) = do
    let name = ty ^. #name
    body <- local (V.cons (name, binding (Proxy :: Proxy Type))) $ nameless (ty ^. #body)
    return . AbstractionType $ #name @= name <: #kind @= ty ^. #kind <: #body @= body <: nil
  nameless (ApplicationType ty) = do
    f <- nameless $ ty ^. #function
    arg <- nameless $ ty ^. #argument
    return . ApplicationType $ #function @= f <: #argument @= arg <: nil
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
  show (RecordTerm fields) = concat ["{", L.intercalate ", " . fmap (\(label, (v, t)) -> concat [show v, show label, ": ", show t]) $ Map.toList fields, "}"]
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
    let name  = t ^. #name
    ty <- nameless $ t ^. #type
    body <- local (V.cons (name, binding (Proxy :: Proxy Term))) $ nameless (t ^. #body)
    return . AbstractionTerm $ #name @= name <: #type @= ty <: #body @= body <: nil
  nameless (ApplicationTerm t) = do
    f <- nameless $ t ^. #function
    arg <- nameless $ t ^. #argument
    return . ApplicationTerm $ #function @= f <: #argument @= arg <: nil
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
    expr <- local (V.cons (t ^. #name, binding (Proxy :: Proxy Term)) . V.cons (t ^. #type, binding (Proxy :: Proxy Type))) $ nameless (t ^. #in)
    return . UnPackageTerm $ #type @= t ^. #type <: #name @= t ^. #name <: #body @= body <: #in @= expr <: nil
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
    expr <- indexMap (c+2) $ t ^. #in
    return . UnPackageTerm $ t & #body .~ body & #in .~ expr
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
  term -> (\term' -> ProjectionTerm $ t & #term .~ term') <$> eval1 term
eval1 (UpdateTerm t) = case t ^. #record of
  RecordTerm fields | all (isVal . snd) fields && isVal new -> 
    case fields Map.!? label of
      Just (v, _) -> return . RecordTerm $ Map.insert label (v, new) fields
      Nothing -> Nothing
  v | isVal v -> (\new' -> UpdateTerm $ t & #new .~ new') <$> eval1 new
  t' -> (\record -> UpdateTerm $ t & #record .~ record) <$> eval1 t'
  where
    new = t ^. #new
    label = t ^. #label
eval1 (TypeApplicationTerm t) = case t ^. #term of
  (TypeAbstractionTerm t') -> Just $ betaReduction (t ^. #type) (t' ^. #body)
  t' -> (\term -> TypeApplicationTerm $ t & #term .~ term) <$> eval1 t'
eval1 (UnPackageTerm t) = case t ^. #body of
  (PackageTerm t') | isVal (t' ^. #term) -> Just $ betaReduction (t' ^. #type) (betaReduction (indexShift 1 (t' ^. #term)) (t ^. #in))
  t' -> (\body -> UnPackageTerm $ t & #body .~ body) <$> eval1 t'
eval1 (PackageTerm t) = (\term -> PackageTerm $ t & #term .~ term) <$> eval1 (t ^. #term)
eval1 _ = Nothing

eval :: UnNamedTerm -> UnNamedTerm
eval t = case eval1 t of
  Just t' -> eval t'
  Nothing -> t

leaveEval :: TypingContext -> NamedTerm -> Either (NameLessErrors TypedBinding) NamedTerm
leaveEval ctx t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ mapLeftDef UnNameError (unName t) >>= mapLeftDef RestoreNameError . restoreName . eval

data KindingError =
    MissingTypeVariableInContextWhileKinding (ContextError 'False TypedBinding)
  | StarKindExpected Kind NamedType NamedType
  | StarKindExpectedAtLabel Kind Variance SString NamedType NamedType
  | ArrowKindExpected Kind NamedType NamedType
  | ApplicationUnMatchedKind Kind Kind NamedType
  | RestoreNameErrorWhileKinding (RestoreNameError TypedBinding)
  deriving (Eq)
instance Show KindingError where
  show (MissingTypeVariableInContextWhileKinding e) = show e
  show (StarKindExpected actual ty whole) = concat ["Couldn't match kind: StarKind Expected, Actual kind = ", show actual, ", ", show ty, " in ", show whole]
  show (StarKindExpectedAtLabel actual v label ty whole) = concat ["Couldn't match kind: StarKind Expected, Actual kind = ", show actual, ", ", show v, show label, ": ", show ty, " in ", show whole]
  show (ArrowKindExpected actual ty whole) = concat ["Couldn't match kind: ArrowKind Expected, Actual kind = ", show actual, ", ", show ty, " in ", show whole]
  show (ApplicationUnMatchedKind domainK argK whole) = concat ["Couldn't match kind: Expected kind = ", show domainK, ", Actual kind = " , show argK, " in ", show whole]
  show (RestoreNameErrorWhileKinding e) = "Warning: In Error Handling: RestoreName Error: " ++ show e

type TypingContext = Context TypedBinding
kinding :: UnNamedType -> Eff '[EitherDef KindingError, ReaderDef TypingContext] Kind
kinding TopType = return StarKind
kinding UnitType = return StarKind
kinding NatType = return StarKind
-- kinding BoolType = return StarKind
kinding (PrimitiveType _) = return StarKind
kinding (VariableType x) = do
  ctx <- ask
  case snd <$> ctx V.!? x of
    Just (VariableTypeBind ty) -> kinding ty
    _ -> throwError . MissingTypeVariableInContextWhileKinding $ MissingVariableInContext x ctx
kinding (ArrowType ty) = do
  let domain = ty ^. #domain
      codomain = ty ^. #codomain
  domainK <- kinding domain
  codomainK <- kinding codomain
  if domainK /= StarKind 
    then failed domain domainK
    else if codomainK /= StarKind
      then failed codomain codomainK
      else return StarKind
  where
    failed ty' k = do
      ty'' <- restoreNameInKinding ty'
      whole <- restoreNameInKinding $ ArrowType ty
      throwError $ StarKindExpected k ty'' whole
kinding (RecordType fields) = Map.foldrWithKey kindcheck (return StarKind) fields
  where
    kindcheck label (v, ty) m = m >> do
      k <- kinding ty
      if k == StarKind
        then return StarKind
        else do
          ty' <- restoreNameInKinding ty
          whole <- restoreNameInKinding $ RecordType fields
          throwError $ StarKindExpectedAtLabel k v label ty' whole
kinding (UniversalType ty) = do
  let name = ty ^. #name
      bound = ty ^. #bound
      body = ty ^. #body
  bodyK <- local (V.cons (name, VariableTypeBind bound)) $ kinding body
  if bodyK == StarKind
    then return StarKind
    else do
      body' <- local (V.cons (name, VariableTypeBind bound)) $ restoreNameInKinding body
      whole <- restoreNameInKinding $ UniversalType ty
      throwError $ StarKindExpected bodyK body' whole
kinding (ExistentialType ty) = do
  let name = ty ^. #name
      bound = ty ^. #bound
      body = ty ^. #body
  bodyK <- local (V.cons (name, VariableTypeBind bound)) $ kinding body
  if bodyK == StarKind
    then return StarKind
    else do
      body' <- local (V.cons (name, VariableTypeBind bound)) $ restoreNameInKinding body
      whole <- restoreNameInKinding $ ExistentialType ty
      throwError $ StarKindExpected bodyK body' whole
kinding (AbstractionType ty) = do
  let k = ty ^. #kind
      top = topOf k
  codomain <- local (V.cons (ty ^. #name, VariableTypeBind top)) $ kinding (ty ^. #body)
  return . ArrowKind $ #domain @= k <: #codomain @= codomain <: nil
kinding (ApplicationType ty) = do
  let f = ty ^. #function
  k1 <- kinding f
  k2 <- kinding $ ty ^. #argument
  case k1 of
    ArrowKind k | k ^. #domain == k2 -> return $ k ^. #codomain
    ArrowKind k -> throwError . ApplicationUnMatchedKind (k ^. #domain) k2 =<< restoreNameInKinding (ApplicationType ty)
    k -> do
      f' <- restoreNameInKinding f
      whole <- restoreNameInKinding $ ApplicationType ty
      throwError $ ArrowKindExpected k f' whole

topOf :: Kind -> Type a
topOf StarKind = TopType
topOf (ArrowKind k) = AbstractionType $ #name @= "_" <: #kind @= k ^. #domain <: #body @= topOf (k ^. #codomain) <: nil

restoreNameInKinding :: NameLess f 'False TypedBinding => f 'False -> Eff '[EitherDef KindingError, ReaderDef TypingContext] (f 'True)
restoreNameInKinding = mapLeftDef RestoreNameErrorWhileKinding . restoreName

data TypingError = 
    MissingDeclarationInTypingContext (ContextError 'True TypedBinding)
  | MissingVariableInTypingContext (ContextError 'False TypedBinding)
  | MissingRecordLabel SString NamedTerm
  | NatTypeExpected NamedType NamedTerm NamedTerm
  | ArrowTypeExpected NamedType NamedTerm NamedTerm
  | RecordTypeExpected NamedType NamedTerm NamedTerm
  | InvariantExpected SString NamedTerm
  | UniversalTypeExpected NamedType NamedTerm NamedTerm
  | ExistentialTypeExpected NamedType NamedTerm NamedTerm
  | ExistentialTypeExpectedAs NamedType NamedTerm
  | SubTypeExpected NamedTerm NamedType NamedType NamedTerm
  | SubTypeExpectedNoTerm NamedType NamedType NamedTerm
  | StarKindExpectedWithTerm Kind NamedType NamedTerm
  | KindingError NamedType NamedTerm KindingError
  | PromotingError PromotingError
  -- | NormalizingError NormalizingError
  | RestoreNameErrorWhileTyping (RestoreNameError TypedBinding)
  deriving (Eq)
instance Show TypingError where
  show (MissingDeclarationInTypingContext e) = "Missing constant declaration: " ++ show e
  show (MissingVariableInTypingContext e) = show e
  show (MissingRecordLabel label whole) = concat ["Record label missing: Label = ", show label, " in ", show whole]
  show (NatTypeExpected actual t whole) = concat ["Couldn't match type: NatType Expected, Actual type = ", show actual, ", ", show t, " in ", show whole]
  show (ArrowTypeExpected actual t whole) = concat ["Couldn't match type: ArrowType Expected, Actual type = ", show actual, ", ", show t, " in ", show whole]
  show (RecordTypeExpected actual t whole) = concat ["Couldn't match type: RecordType Expected, Actual type = ", show actual, ", ", show t, " in ", show whole]
  show (InvariantExpected label whole) = concat ["Couldn't update record: Label = ", show label, " in ", show whole]
  show (UniversalTypeExpected actual t whole) = concat ["Couldn't match type: UniversalType Expected, Actual type = ", show actual, ", ", show t, " in ", show whole]
  show (ExistentialTypeExpected actual t whole) = concat ["Couldn't match type: ExistentialType Expected, Actual type = ", show actual, ", ", show t, " in ", show whole]
  show (ExistentialTypeExpectedAs actual whole) = concat ["Couldn't match type: ExistentialType Expected, Actual type = ", show actual, " in ", show whole]
  show (SubTypeExpected t1 ty1 ty2 whole) = concat ["Couldn't match subtype: ", show t1, ": ", show ty1, " should be subtype of ", show ty2, " in ", show whole]
  show (SubTypeExpectedNoTerm ty1 ty2 whole) = concat ["Couldn't match subtype: ", show ty1, "should be subtype of ", show ty2, " in ", show whole]
  show (StarKindExpectedWithTerm actual ty whole) = concat ["Couldn't match kind: StarKind Expected, Actual kind = ", show actual, ", ", show ty, " in ", show whole]
  show (KindingError ty whole e) = concat ["Kinding Error: " ++ show e, " at ", show ty, " in ", show whole]
  show (PromotingError e) = "Promoting Error: " ++ show e
  show (RestoreNameErrorWhileTyping e) = "Warning: In Error Handling: RestoreName Error: " ++ show e


typing :: UnNamedTerm -> Eff '[EitherDef TypingError, ReaderDef TypingContext] UnNamedType
typing Unit = return UnitType
typing Zero = return NatType
typing (Succ t) = do
  ty <- typing t
  mapLeftDef PromotingError (ty `isSubTypeOf` NatType) >>= 
    bool
      (failed ty)
      (return NatType)
  where
    failed ty = do
      t'     <- restoreNameInTyping t
      actual <- restoreNameInTyping ty
      throwError $ NatTypeExpected actual t' (Succ t')
typing (ConstTerm s) = do
  ctx <- ask
  case snd <$> V.find ((==) s . fst) ctx of
    Just (ConstTermBind ty) -> return ty
    _ -> throwError $ MissingDeclarationInTypingContext (MissingVariableInContext s ctx)
typing (VariableTerm x) = do
  ctx <- ask
  case ctx V.!? x of
    Just (_, VariableTermBind ty) -> return $ indexShift (x+1) ty
    _ -> throwError $ MissingVariableInTypingContext (MissingVariableInContext x ctx)
typing (AbstractionTerm t) = do
  let domain = t ^. #type
  whole <- restoreNameInTyping $ AbstractionTerm t
  domain' <- restoreNameInTyping domain
  k <- mapLeftDef (KindingError domain' whole) $ kinding domain
  if k /= StarKind
    then failed k domain
    else do
      codomain <- local (V.cons (t ^. #name, VariableTermBind domain)) $ typing (t ^. #body)
      return . ArrowType $ #domain @= domain <: #codomain @= indexShift (-1) codomain <: nil
  where
    failed k ty = do
      ty'   <- restoreNameInTyping ty
      whole <- restoreNameInTyping $ AbstractionTerm t
      throwError $ StarKindExpectedWithTerm k ty' whole
typing (ApplicationTerm t) = do
  ty1 <- castEff . expose =<< typing (t ^. #function)
  ty2 <- typing $ t ^. #argument
  case ty1 of
    ArrowType ty1' -> do
      let domain = ty1' ^. #domain
      mapLeftDef PromotingError (ty2 `isSubTypeOf` domain) >>=
        bool 
          (failed1 ty2 domain)
          (return $ ty1' ^. #codomain)
    _ -> failed2 ty1
  where
    failed1 arg domain = do
      t1'    <- restoreNameInTyping $ t ^. #argument
      arg'   <- restoreNameInTyping arg
      domain'   <- restoreNameInTyping domain
      whole <- restoreNameInTyping $ ApplicationTerm t
      throwError $ SubTypeExpected t1' arg' domain' whole
    failed2 ty1 = do
      actual <- restoreNameInTyping ty1
      f      <- restoreNameInTyping $ t ^. #function
      whole  <- restoreNameInTyping $ ApplicationTerm t
      throwError $ ArrowTypeExpected actual f whole
typing (RecordTerm fields) = RecordType <$> mapM (traverse typing) fields
typing (ProjectionTerm t) = do
  ty <- castEff . expose =<< typing (t ^. #term)
  case ty of
    RecordType fields -> case fields Map.!? (t ^. #label) of
      Just (_, ty') -> return ty'
      Nothing -> throwError . MissingRecordLabel (t ^. #label) =<< restoreNameInTyping (ProjectionTerm t)
    _ -> do
      actual <- restoreNameInTyping ty
      term   <- restoreNameInTyping $ t ^. #term
      whole  <- restoreNameInTyping $ ProjectionTerm t
      throwError $ RecordTypeExpected actual term whole
typing (UpdateTerm t) = do
  record <- castEff . expose =<< typing (t ^. #record)
  new <- typing $ t ^. #new
  case record of
    RecordType fields -> 
      case fields Map.!? (t ^. #label) of
        Just (v, old) 
          | v /= Covariant -> throwError . InvariantExpected (t ^. #label) =<< restoreNameInTyping (UpdateTerm t)
          | otherwise ->
            mapLeftDef PromotingError (new `isSubTypeOf` old) >>= 
            bool
              (failed1 new old)
              (return record)
        _ -> failed2
    _ -> failed3 record
  where
    failed1 new old = do
      t1    <- restoreNameInTyping $ t ^. #new
      new'  <- restoreNameInTyping new
      old'  <- restoreNameInTyping old
      whole <- restoreNameInTyping $ UpdateTerm t
      throwError $ SubTypeExpected t1 new' old' whole
    failed2 = throwError . MissingRecordLabel (t ^. #label) =<< restoreNameInTyping (UpdateTerm t)
    failed3 record = do
      actual <- restoreNameInTyping record
      term   <- restoreNameInTyping $ t ^. #record
      whole  <- restoreNameInTyping $ UpdateTerm t
      throwError $ RecordTypeExpected actual term whole
typing (TypeAbstractionTerm t) = do
  let x = t ^. #name
      bound = t ^. #bound
  body <- local (V.cons (x, VariableTypeBind bound)) $ typing (t ^. #body)
  return . UniversalType $ #name @= x <: #bound @= bound <: #body @= body <: nil
typing (TypeApplicationTerm t) = do
  let ty = t ^. #type
  term <- castEff . expose =<< typing (t ^. #term)
  case term of
    UniversalType ty' ->
      let bound = ty' ^. #bound in
      mapLeftDef PromotingError (ty `isSubTypeOf` bound) >>=
      bool
        (failed1 ty bound)
        (return $ betaReduction ty (ty' ^. #body))
    _ -> failed2 term
  where
    failed1 ty bound = do
      ty1 <- restoreNameInTyping ty
      ty2 <- restoreNameInTyping bound
      whole <- restoreNameInTyping $ TypeApplicationTerm t
      throwError $ SubTypeExpectedNoTerm ty1 ty2 whole
    failed2 term = do
      actual <- restoreNameInTyping term
      t' <- restoreNameInTyping $ t ^. #term
      whole <- restoreNameInTyping $ TypeApplicationTerm t
      throwError $ UniversalTypeExpected actual t' whole
typing (PackageTerm t) = do
  let exist = t ^. #exist
  whole <- restoreNameInTyping $ PackageTerm  t
  exist' <- restoreNameInTyping exist
  k <- mapLeftDef (KindingError exist' whole) $ kinding exist
  if k /= StarKind
    then throwError $ StarKindExpectedWithTerm k exist' whole
    else do
      ty <- castEff $ normalize exist
      case ty of
        ExistentialType ty' ->
          let bound = ty' ^. #bound in
          mapLeftDef PromotingError ((t ^. #type) `isSubTypeOf` bound) >>=
            bool
              (failed1 bound)
              (do
                let concrete = betaReduction (t ^. #type) exist
                term <- typing $ t ^. #term
                mapLeftDef PromotingError (term `isSubTypeOf` concrete) >>=
                  bool
                    (failed2 term concrete)
                    (return exist))
        ty' -> failed3 ty'
  where
    failed1 bound = do
      ty' <- restoreNameInTyping $ t ^. #type
      bound' <- restoreNameInTyping bound
      whole <- restoreNameInTyping $ PackageTerm t
      throwError $ SubTypeExpectedNoTerm ty' bound' whole
    failed2 term concrete = do
      t' <- restoreNameInTyping $ t ^. #term
      term' <- restoreNameInTyping term
      concrete' <- restoreNameInTyping concrete
      whole <- restoreNameInTyping $ PackageTerm t
      throwError $ SubTypeExpected t' term' concrete' whole
    failed3 ty = do
      actual <- restoreNameInTyping ty
      whole <- restoreNameInTyping $ PackageTerm t
      throwError $ ExistentialTypeExpectedAs actual whole
typing (UnPackageTerm t) = do
  let body = t ^. #body
  ty <- castEff . expose =<< typing body
  case ty of
    ExistentialType ty' -> indexShift (-2) <$> local (V.cons (t ^. #name, VariableTermBind (ty' ^. #body)) . V.cons (t ^. #type, VariableTypeBind (ty' ^. #bound))) (typing (t ^. #in))
    _ -> do
      actual <- restoreNameInTyping ty
      body' <- restoreNameInTyping body
      whole <- restoreNameInTyping $ UnPackageTerm t
      throwError $ ExistentialTypeExpected actual body' whole

restoreNameInTyping :: NameLess f 'False TypedBinding => f 'False -> Eff '[EitherDef TypingError, ReaderDef TypingContext] (f 'True)
restoreNameInTyping = mapLeftDef RestoreNameErrorWhileTyping . restoreName

leaveTyping :: TypingContext -> NamedTerm -> Either Errors NamedType
leaveTyping ctx t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ do
  t' <- mapLeftDef (NameLessError . UnNameError) $ unName t
  ty <- mapLeftDef TypingError $ typing t'
  mapLeftDef (NameLessError . RestoreNameError) $ restoreName ty
 

expose :: UnNamedType -> Eff '[ReaderDef TypingContext] UnNamedType
expose ty = fmap (either (const ty) id) . runEitherDef $ promoteVariable =<< castEff (normalize ty)

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
-- data NormalizingError = MissingTypeAbbreviation (Named 'False) TypingContext
normalize :: UnNamedType -> Eff '[ReaderDef TypingContext] UnNamedType
normalize (VariableType x) = do
  ctx <- ask
  case ctx V.!? x of
    Just (_, TypeAbbreviationBind ty) -> normalize ty
    _ -> return $ VariableType x
normalize (ApplicationType ty) = do
  f <- normalize $ ty ^. #function
  case f of
    AbstractionType ty' -> normalize $ betaReduction (ty ^. #argument) (ty' ^. #body)
    _ -> return . ApplicationType $ ty & #function .~ f
normalize ty = return ty
leaveNormalize :: TypingContext -> NamedType -> Either (NameLessErrors TypedBinding) NamedType
leaveNormalize ctx ty = leaveEff . (`runReaderDef` ctx) . runEitherDef $ mapLeftDef UnNameError (unName ty) >>= castEff . normalize >>=  mapLeftDef RestoreNameError . restoreName 

isSubTypeOf :: UnNamedType -> UnNamedType -> Eff '[EitherDef PromotingError, ReaderDef TypingContext] Bool
isSubTypeOf ty1 ty2 =
  castEff (ty1 `isEquivalentTo` ty2) >>=
    flip bool
      (return True)
      (do
        ty1' <- castEff $ normalize ty1
        ty2' <- castEff $ normalize ty2
        case (ty1', ty2') of
          (_, TopType) -> return True
          (VariableType _, _) -> promoteVariable ty1' >>= (`isSubTypeOf` ty2')
          (ArrowType ty1'', ArrowType ty2'') -> (&&) <$> ((ty1'' ^. #domain) `isSubTypeOf` (ty2'' ^. #domain)) <*> ((ty1'' ^. #codomain) `isSubTypeOf` (ty2'' ^. #codomain))
          (RecordType fields1, RecordType fields2) -> Map.foldrWithKey isSubTypeFieldOf (return True) fields2
            where
              isSubTypeFieldOf label (v2, ty2'') mb = 
                case fields1 Map.!? label of
                  Just (v1, ty1'') | v1 == Invariant || v2 == Covariant -> 
                    (&&) <$> mb <*> (ty1'' `isSubTypeOf` ty2'')
                  _ -> return False
          (UniversalType ty1'', UniversalType ty2'') -> do
            let bound1 = ty1'' ^. #bound
                bound2 = ty2'' ^. #bound
            b1 <- (&&) <$> (bound1 `isSubTypeOf` bound2) <*> (bound2 `isSubTypeOf` bound1) -- equivalent??
            b2 <- local (V.cons (mconcat [ty1'' ^. #name, "_", ty2'' ^. #name], VariableTypeBind bound1)) $ (ty1'' ^. #body) `isSubTypeOf` (ty2'' ^. #body)
            return $ b1 && b2
          (ExistentialType ty1'', ExistentialType ty2'') -> do
            let bound1 = ty1'' ^. #bound
                bound2 = ty2'' ^. #bound
            b1 <- (&&) <$> (bound1 `isSubTypeOf` bound2) <*> (bound2 `isSubTypeOf` bound1) -- equivalent??
            b2 <- local (V.cons (mconcat [ty1'' ^. #name, "_", ty2'' ^. #name], VariableTypeBind bound1)) $ (ty1'' ^. #body) `isSubTypeOf` (ty2'' ^. #body)
            return $ b1 && b2
          (AbstractionType ty1'', AbstractionType ty2'') -> do
            let k = ty1'' ^. #kind
            b <- local (V.cons (mconcat [ty1'' ^. #name, "_", ty2'' ^. #name], VariableTypeBind (topOf k))) $ (ty1'' ^. #body) `isSubTypeOf` (ty2'' ^. #body)
            return $ (k == ty2'' ^. #kind) && b
          (ApplicationType _, _) -> promoteVariable ty1' >>= (`isSubTypeOf` ty2')
          _ -> return False)

isEquivalentTo :: UnNamedType -> UnNamedType -> Eff '[ReaderDef TypingContext] Bool
isEquivalentTo ty1 ty2 = do
  ty1' <- castEff $ normalize ty1
  ty2' <- castEff $ normalize ty2
  case (ty1', ty2') of
    (TopType, TopType) -> return True
    (UnitType, UnitType) -> return True
    (NatType, NatType) -> return True
    (PrimitiveType s1, PrimitiveType s2) -> return $ s1 == s2
    (VariableType x, VariableType y) -> return $ x == y
    (ArrowType ty1'', ArrowType ty2'') -> (&&) <$> ((ty1'' ^. #domain) `isEquivalentTo` (ty2'' ^. #domain)) <*> ((ty1'' ^. #codomain) `isEquivalentTo` (ty2'' ^. #codomain))
    (RecordType fields1, RecordType fields2) -> zipFold (Map.toList fields1) (Map.toList fields2)
    (UniversalType ty1'', UniversalType ty2'') -> (&&) <$> ((ty1'' ^. #bound) `isEquivalentTo` (ty2'' ^. #bound)) <*> ((ty1'' ^. #body) `isEquivalentTo` (ty2'' ^. #body))
    (ExistentialType ty1'', ExistentialType ty2'') -> (&&) <$> ((ty1'' ^. #bound) `isEquivalentTo` (ty2'' ^. #bound)) <*> ((ty1'' ^. #body) `isEquivalentTo` (ty2'' ^. #body))
    (AbstractionType ty1'', AbstractionType ty2'') -> (&&) (ty1'' ^. #kind == ty2'' ^. #kind) <$> ((ty1'' ^. #body) `isEquivalentTo` (ty2'' ^. #body))
    (ApplicationType ty1'', ApplicationType ty2'') -> (&&) <$> ((ty1'' ^. #function) `isEquivalentTo` (ty2'' ^. #function)) <*> ((ty1'' ^. #argument) `isEquivalentTo` (ty2'' ^. #argument))
    _ -> return False
  where
    zipFold ((k1, (v1, ty1')):xs1) ((k2, (v2, ty2')):xs2) | k1 == k2 && v1 == v2 = (&&) <$> ty1' `isEquivalentTo` ty2' <*> zipFold xs1 xs2
    zipFold [] [] = return True
    zipFold _ _ = return False

leaveIsSubTypeOf :: TypingContext -> NamedType -> NamedType -> Either Errors Bool
leaveIsSubTypeOf ctx ty1 ty2 = leaveEff . (`runReaderDef` ctx) . runEitherDef $ do
  ty1' <- mapLeftDef (NameLessError . UnNameError) $ unName ty1
  ty2' <- mapLeftDef (NameLessError . UnNameError) $ unName ty2
  mapLeftDef (TypingError . PromotingError) $ ty1' `isSubTypeOf` ty2'
