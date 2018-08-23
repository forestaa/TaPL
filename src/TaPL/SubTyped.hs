{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}

module TaPL.SubTyped where

import RIO
import qualified RIO.Vector as V
import qualified RIO.Map as Map

import Control.Lens hiding ((^.))
import Control.Monad.Error.Class
import Control.Monad.State.Strict

import Data.Extensible.Effect
import Data.Extensible.Effect.Default
-- import qualified Data.Set as S
-- import qualified Data.List as L
-- import qualified Data.Map.Strict as M


data Ty = TyTop | TyArrow Ty Ty | TyRecord (Map.Map String Ty) deriving (Show, Eq)

type DeBrujinIndex = Int
data NamedTerm = 
    TmVar String 
  | TmAbs String Ty NamedTerm 
  | TmApp NamedTerm NamedTerm
  | TmRecord (Map.Map String NamedTerm)
  | TmProj NamedTerm String
  deriving (Show, Eq)
data UnNamedTerm = 
    TmVar' DeBrujinIndex
  | TmAbs' String Ty UnNamedTerm
  | TmApp' UnNamedTerm UnNamedTerm
  | TmRecord' (Map.Map String UnNamedTerm)
  | TmProj' UnNamedTerm String
  deriving (Show, Eq)
type NamingContext = Vector (String, Binding)
data Binding = NamedBind | VarBind Ty deriving (Show, Eq)
data Errors = 
    RemoveNamesError RemoveNamesError 
  | RestoreNamesError RestoreNamesError
  | TypingError TypingError
  | EvalError EvalError 
  deriving (Show, Eq)
data RemoveNamesError = MissingVariableInNamingContextInRemoving String NamingContext deriving (Eq)
data RestoreNamesError = MissingVariableInNamingContextInRestoring String NamingContext deriving (Eq)
data TypingError = 
    MissingTypeInNamingContext String 
  | NotMatchedTypeTmApp UnNamedTerm Ty UnNamedTerm Ty
  | NotMatchedTypeTyProjLabelMissing String (Map.Map String Ty)
  | NotMatchedTypeTyProjNotRecord
  deriving (Eq)
data EvalError = NoRuleApplies deriving (Show, Eq)

instance Show RemoveNamesError where
  show (MissingVariableInNamingContextInRemoving x ctx) = concat ["missing variable in naming context: variable: ", x, ", NamingContext: ", show ctx]
instance Show RestoreNamesError where
  show (MissingVariableInNamingContextInRestoring x ctx) = concat ["missing variable in naming context: variable: ", x, ", NamingContext: ", show ctx]
instance Show TypingError where
  show (MissingTypeInNamingContext x) = concat ["missing type in naming context: ", x]
  show (NotMatchedTypeTmApp t1 ty1 t2 ty2) = concat ["doesn't matched type: application: t1 = ", show t1, ", ty1 = ", show ty1, ", t2 = ", show t2, ", ty2 = ", show ty2]
  show (NotMatchedTypeTyProjLabelMissing label fields) = concat ["missing label in fields: label = ", label, ", fields", show fields]
  show NotMatchedTypeTyProjNotRecord = "projection: not record type"
  

removeNamesWithContext :: NamingContext -> NamedTerm -> Eff '[EitherDef Errors] UnNamedTerm
removeNamesWithContext ctx = (`evalStateDef` ctx) . removeNamesWithContext'

removeNamesWithContext' :: NamedTerm -> Eff '[StateDef NamingContext, EitherDef Errors] UnNamedTerm
removeNamesWithContext' (TmVar x) = do
  maybei <- gets (V.findIndex ((==) x . (^. _1)))
  case maybei of
    Just i -> return $ TmVar' i
    Nothing -> get >>= throwError . RemoveNamesError . MissingVariableInNamingContextInRemoving x
removeNamesWithContext' (TmAbs x ty t) = modify (V.cons (x, VarBind ty)) >> fmap (TmAbs' x ty) (removeNamesWithContext' t)
removeNamesWithContext' (TmApp t1 t2) = do
  ctx <- get
  t1' <- castEff $ evalStateDef (removeNamesWithContext' t1) ctx
  t2' <- castEff $ evalStateDef (removeNamesWithContext' t2) ctx
  return $ TmApp' t1' t2'
removeNamesWithContext' (TmRecord fields) = do
  ctx <- get
  castEff . fmap TmRecord' $ mapM (flip evalStateDef ctx . removeNamesWithContext') fields
removeNamesWithContext' (TmProj t label) = do
  t' <- removeNamesWithContext' t
  return $ TmProj' t' label


restoreNamesWithContext :: NamingContext -> UnNamedTerm -> Eff '[EitherDef Errors] NamedTerm
restoreNamesWithContext ctx = (`evalStateDef` ctx) . restoreNamesWithContext'

restoreNamesWithContext' :: UnNamedTerm -> Eff '[StateDef NamingContext, EitherDef Errors] NamedTerm
restoreNamesWithContext' (TmVar' n) = do
  ctx <- get
  case ctx V.!? n of
    Just (name, _) -> return $ TmVar name
    Nothing -> throwError . RestoreNamesError $ MissingVariableInNamingContextInRestoring (show n) ctx
restoreNamesWithContext' (TmAbs' x ty t) = modify (V.cons (x, VarBind ty)) >> fmap (TmAbs x ty) (restoreNamesWithContext' t)
restoreNamesWithContext' (TmApp' t1 t2) = do
  ctx <- get
  t1' <- castEff $ evalStateDef (restoreNamesWithContext' t1) ctx
  t2' <- castEff $ evalStateDef (restoreNamesWithContext' t2) ctx
  return $ TmApp t1' t2'
restoreNamesWithContext' (TmRecord' fields) = do
  ctx <- get
  castEff . fmap TmRecord $ mapM (flip evalStateDef ctx . restoreNamesWithContext') fields
restoreNamesWithContext' (TmProj' t label) = do
  t' <- restoreNamesWithContext' t
  return $ TmProj t' label

typeOf :: NamingContext -> UnNamedTerm -> Eff '[EitherDef Errors] Ty
typeOf ctx = (`evalStateDef` ctx) . typeOf'

typeOf' :: UnNamedTerm -> Eff [StateDef NamingContext, EitherDef Errors] Ty
typeOf' (TmVar' n) = do
  ctx <- get
  case ctx V.!? n of
    Just (_, VarBind ty) -> return ty
    _ -> throwError . TypingError $ MissingTypeInNamingContext (show n)
  -- binding <- gets ((^. _2) . (!! n))
  -- case binding of
  --   VarBind ty -> return ty
  --   _ -> gets ((^. _1) . (!! n)) >>= throwError . TypingError . MissingTypeInNamingContext 
typeOf' (TmAbs' x ty t) = modify (V.cons (x, VarBind ty)) >> fmap (TyArrow ty) (typeOf' t)
typeOf' (TmApp' t1 t2) = do
  ctx <- get
  ty1 <- castEff $ evalStateDef (typeOf' t1) ctx
  ty2 <- castEff $ evalStateDef (typeOf' t2) ctx
  case ty1 of
    TyArrow ty1' ty2'
      | isSubType ty2 ty1' -> return ty2'
    _ -> throwError . TypingError $ NotMatchedTypeTmApp t1 ty1 t2 ty2
typeOf' (TmRecord' fields) = do
  ctx <- get
  castEff . fmap TyRecord $ mapM (flip evalStateDef ctx . typeOf') fields
typeOf' (TmProj' t label) = do
  ty <- typeOf' t
  case ty  of
    TyRecord fields ->
      case fields Map.!? label of
        Just ty' -> return ty'
        _ -> throwError . TypingError $ NotMatchedTypeTyProjLabelMissing label fields
    _ -> throwError $ TypingError NotMatchedTypeTyProjNotRecord


isSubType :: Ty -> Ty -> Bool
isSubType tyS tyT | tyS == tyT = True
isSubType _ TyTop = True
isSubType (TyArrow tyS1 tyS2) (TyArrow tyT1 tyT2) = isSubType tyT1 tyS1 && isSubType tyS2 tyT2
isSubType (TyRecord fieldS) (TyRecord fieldT) = Map.foldrWithKey isSubTypeField True fieldT
  where
    isSubTypeField _ _ False = False
    isSubTypeField label t True = 
      case fieldS Map.!? label of
        Just t' -> isSubType t' t
        Nothing -> False
isSubType _ _ = False

termShift :: DeBrujinIndex -> UnNamedTerm -> UnNamedTerm
termShift d = walk 0
  where
    walk c (TmVar' n) | n < c = TmVar' n
                      | otherwise = TmVar' (n + d)
    walk c (TmAbs' x ty t) = TmAbs' x ty $ walk (c+1) t
    walk c (TmApp' t1 t2) = TmApp' (walk c t1) (walk c t2)
    walk c (TmRecord' fields) = TmRecord' $ fmap (walk c) fields
    walk c (TmProj' t label) = TmProj' (walk c t) label

termSubst :: DeBrujinIndex -> UnNamedTerm -> UnNamedTerm -> UnNamedTerm
termSubst j s (TmVar' n) | n == j    = s
                         | otherwise = TmVar' n
termSubst j s (TmAbs' x ty t) = TmAbs' x ty $ termSubst (j + 1) (termShift 1 s) t
termSubst j s (TmApp' t1 t2) = TmApp' (termSubst j s t1) (termSubst j s t2)
termSubst j s (TmRecord' fields) = TmRecord' $ fmap (termSubst j s) fields
termSubst j s (TmProj' t label) = TmProj' (termSubst j s t) label

betaReduction :: UnNamedTerm -> UnNamedTerm -> UnNamedTerm
betaReduction s t = termShift (-1) $ termSubst 0 (termShift 1 s) t

isVal :: UnNamedTerm -> Bool
isVal (TmAbs' _ _ _) = True
isVal (TmRecord' _) = True
isVal _ = False 

eval1 :: UnNamedTerm -> Eff '[EitherDef Errors] UnNamedTerm
eval1 (TmApp' (TmAbs' _ _ t1) v2) | isVal v2 = return $ betaReduction v2 t1
eval1 (TmApp' v1 t2) | isVal v1 = TmApp' v1 <$> eval1 t2
eval1 (TmApp' t1 t2) = (`TmApp'` t2) <$> eval1 t1
eval1 (TmRecord' fields) = TmRecord' . Map.fromList <$> eval1Record (Map.toList fields)
  where
    eval1Record [] = throwError $ EvalError NoRuleApplies
    eval1Record ((label, t):rest) = evalRecordBody label t rest `catchError` handler label t rest
    evalRecordBody label t rest = do
      t' <- eval1 t
      return $ (label, t'):rest
    handler label t rest (EvalError NoRuleApplies) = (:) (label, t) <$> eval1Record rest
    handler _ _ _ e = throwError e
eval1 (TmProj' (TmRecord' fields) label) = case fields Map.!? label of
  Just term -> return term 
  Nothing -> throwError $ EvalError NoRuleApplies
eval1 (TmProj' t label) = flip TmProj' label <$> eval1 t
eval1 _ = throwError $ EvalError NoRuleApplies

eval' :: UnNamedTerm -> Eff '[EitherDef Errors] UnNamedTerm
eval' t = (eval1 t >>= eval') `catchError` handler
  where
    handler (EvalError NoRuleApplies) = return t
    handler e = throwError e

eval :: NamingContext -> NamedTerm -> Either Errors (NamedTerm, Ty)
eval ctx t = leaveEff $ runEitherDef ret
  where
    ret = do
      t1 <- removeNamesWithContext ctx t
      ty <- typeOf ctx t1
      t2 <- eval' t1
      t3 <- restoreNamesWithContext ctx t2
      return (t3, ty)