{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}

module TaPL.SubTyped where

import Control.Lens
import Control.Monad.Error.Class
import Control.Monad.State.Strict

import Data.Extensible.Effect
import Data.Extensible.Effect.Default
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Map.Strict as M


data Ty = TyTop | TyArrow Ty Ty | TyRecord (M.Map String Ty) deriving (Show, Eq)

type DeBrujinIndex = Int
data NamedTerm = 
    TmVar String 
  | TmAbs String Ty NamedTerm 
  | TmApp NamedTerm NamedTerm
  | TmRecord (M.Map String NamedTerm)
  | TmProj NamedTerm String
  deriving (Show)
data UnNamedTerm = 
    TmVar' DeBrujinIndex
  | TmAbs' String Ty UnNamedTerm
  | TmApp' UnNamedTerm UnNamedTerm
  | TmRecord' (M.Map String UnNamedTerm)
  | TmProj' UnNamedTerm String
  deriving (Show)
type NamingContext = [(String, Binding)]
data Binding = NamedBind | VarBind Ty deriving Show
data Errors = 
    RemoveNamesError RemoveNamesError 
  | TypingError TypingError
  | EvalError EvalError 
  deriving Show
data RemoveNamesError = MissingVariableInNamingContext String NamingContext
data TypingError = 
    MissingTypeInNamingContext String 
  | NotMatchedTypeTmApp UnNamedTerm Ty UnNamedTerm Ty
  | NotMatchedTypeTyProjLabelMissing String (M.Map String Ty)
  | NotMatchedTypeTyProjNotRecord
data EvalError = NoRuleApplies deriving Show

instance Show RemoveNamesError where
  show (MissingVariableInNamingContext x ctx) = concat ["missing variable in naming context: variable: ", x, ", NamingContext: ", show ctx]
instance Show TypingError where
  show (MissingTypeInNamingContext x) = concat ["missing type in naming context: ", x]
  show (NotMatchedTypeTmApp t1 ty1 t2 ty2) = concat ["doesn't matched type: application: t1 = ", show t1, ", ty1 = ", show ty1, ", t2 = ", show t2, ", ty2 = ", show ty2]
  show (NotMatchedTypeTyProjLabelMissing label fields) = concat ["missing label in fields: label = ", label, ", fields", show fields]
  show NotMatchedTypeTyProjNotRecord = "projection: not record type"
  

removeNamesWithContext :: NamingContext -> NamedTerm -> Eff '[EitherDef Errors] UnNamedTerm
removeNamesWithContext ctx = (`evalStateDef` ctx) . removeNamesWithContext'

removeNamesWithContext' :: NamedTerm -> Eff '[StateDef NamingContext, EitherDef Errors] UnNamedTerm
removeNamesWithContext' (TmVar x) = do
  maybei <- gets (L.findIndex ((==) x . (^. _1)))
  case maybei of
    Just i -> return $ TmVar' i
    Nothing -> get >>= throwError . RemoveNamesError . MissingVariableInNamingContext x
removeNamesWithContext' (TmAbs x ty t) = modify ((:) (x, VarBind ty)) >> fmap (TmAbs' x ty) (removeNamesWithContext' t)
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


restoreNamesWithContext :: NamingContext -> UnNamedTerm -> NamedTerm
restoreNamesWithContext ctx = leaveEff . (`evalStateDef` ctx) . restoreNamesWithContext'

restoreNamesWithContext' :: UnNamedTerm -> Eff '[StateDef NamingContext] NamedTerm
restoreNamesWithContext' (TmVar' n) = gets (TmVar . (^. _1) . (!! n))
restoreNamesWithContext' (TmAbs' x ty t) = modify ((:) (x, VarBind ty)) >> fmap (TmAbs x ty) (restoreNamesWithContext' t)
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
  binding <- gets ((^. _2) . (!! n))
  case binding of
    VarBind ty -> return ty
    _ -> gets ((^. _1) . (!! n)) >>= throwError . TypingError . MissingTypeInNamingContext 
typeOf' (TmAbs' x ty t) = modify ((:) (x, VarBind ty)) >> fmap (TyArrow ty) (typeOf' t)
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
      case fields M.!? label of
        Just ty' -> return ty'
        _ -> throwError . TypingError $ NotMatchedTypeTyProjLabelMissing label fields
    _ -> throwError $ TypingError NotMatchedTypeTyProjNotRecord


isSubType :: Ty -> Ty -> Bool
isSubType tyS tyT | tyS == tyT = True
isSubType _ TyTop = True
isSubType (TyArrow tyS1 tyS2) (TyArrow tyT1 tyT2) = isSubType tyT1 tyS1 && isSubType tyS2 tyT2
isSubType (TyRecord fieldS) (TyRecord fieldT) = M.foldrWithKey isSubTypeField True fieldT
  where
    isSubTypeField _ _ False = False
    isSubTypeField label t True = 
      case fieldS M.!? label of
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
termSubst j s (TmAbs' x ty t) = TmAbs' x ty $ termSubst (succ j) (termShift 1 s) t
termSubst j s (TmApp' t1 t2) = TmApp' (termSubst j s t1) (termSubst j s t2)
termSubst j s (TmRecord' fields) = TmRecord' $ fmap (termSubst j s) fields
termSubst j s (TmProj' t label) = TmProj' (termSubst j s t) label

betaReduction :: UnNamedTerm -> UnNamedTerm -> UnNamedTerm
betaReduction s t = termShift (-1) $ termSubst 0 (termShift 1 s) t

eval1 :: UnNamedTerm -> Eff '[EitherDef Errors] UnNamedTerm
eval1 (TmApp' (TmAbs' _ _ t1) v2@(TmAbs' _ _ _)) = return $ betaReduction v2 t1
eval1 (TmApp' v1@(TmAbs' _ _ _) t2) = TmApp' v1 <$> eval1 t2
eval1 (TmApp' t1 t2) = (`TmApp'` t2) <$> eval1 t1
eval1 (TmRecord' fields) = TmRecord' . M.fromList <$> eval1Record (M.toList fields)
  where
    eval1Record [] = throwError $ EvalError NoRuleApplies
    evalRecord ((label, t):rest) = evalRecordBody label t rest `catchError` handler label t rest
    evalRecordBody label t rest = do
      t' <- eval1 t
      return $ (label, t'):rest
    handler label t rest (EvalError NoRuleApplies) = (:) (label, t) <$> evalRecord rest
    handler _ _ _ e = throwError e
eval1 (TmProj' (TmRecord' fields) label) | label `L.elem` M.keys fields = return $ fields M.! label
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
      let t3 = restoreNamesWithContext ctx t2
      return (t3, ty)