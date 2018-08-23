{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}

module TaPL.SimplyTyped where

import RIO
import qualified RIO.Vector as V

import Control.Lens hiding ((^.))
import Control.Monad.Error.Class
import Control.Monad.State.Strict

import Data.Extensible.Effect
import Data.Extensible.Effect.Default


data Ty = TyArrow Ty Ty | TyBool deriving (Show, Eq)

type DeBrujinIndex = Int
data NamedTerm = 
    TmVar String 
  | TmAbs String Ty NamedTerm 
  | TmApp NamedTerm NamedTerm
  | TmTrue
  | TmFalse
  | TmIf NamedTerm NamedTerm NamedTerm
  deriving (Show, Eq)
data UnNamedTerm = 
    TmVar' DeBrujinIndex
  | TmAbs' String Ty UnNamedTerm
  | TmApp' UnNamedTerm UnNamedTerm
  | TmTrue'
  | TmFalse'
  | TmIf' UnNamedTerm UnNamedTerm UnNamedTerm
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
data RestoreNamesError = MissingVariableInNamingContextInRestoring DeBrujinIndex NamingContext deriving (Eq)
data TypingError = 
    MissingTypeInNamingContext String 
  | NotMatchedTypeTmApp UnNamedTerm Ty UnNamedTerm Ty
  | NotMatchedTypeTmIfT1 UnNamedTerm Ty
  | NotMatchedTypeTmIfT2T3 UnNamedTerm Ty UnNamedTerm Ty
  deriving (Eq)
data EvalError = NoRuleApplies deriving (Show, Eq)

instance Show RemoveNamesError where
  show (MissingVariableInNamingContextInRemoving x ctx) = concat ["missing variable in naming context: variable: ", x, ", NamingContext: ", show ctx]
instance Show RestoreNamesError where
  show (MissingVariableInNamingContextInRestoring x ctx) = concat ["missing variable in naming context: variable: ", show x, ", NamingContext: ", show ctx]
instance Show TypingError where
  show (MissingTypeInNamingContext x) = concat ["missing type in naming context: ", x]
  show (NotMatchedTypeTmApp t1 ty1 t2 ty2) = concat ["doesn't matched type: application: t1 = ", show t1, ", ty1 = ", show ty1, ", t2 = ", show t2, ", ty2 = ", show ty2]
  show (NotMatchedTypeTmIfT1 t1 ty1) = concat ["doesn't matched type: if: t1 should be bool: t1 = ", show t1, ", ty1 = ", show ty1]
  show (NotMatchedTypeTmIfT2T3 t2 ty2 t3 ty3) = concat ["doesn't matched type: if: the types of t2 and t3 should be the same: t2 = ", show t2, ", ty2 = ", show ty2, "t3 = ", show t3, ", ty3 = ", show ty3]
  

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
removeNamesWithContext' TmTrue = return TmTrue'
removeNamesWithContext' TmFalse = return TmFalse'
removeNamesWithContext' (TmIf t1 t2 t3) = do
  ctx <- get
  t1' <- castEff $ evalStateDef (removeNamesWithContext' t1) ctx
  t2' <- castEff $ evalStateDef (removeNamesWithContext' t2) ctx
  t3' <- castEff $ evalStateDef (removeNamesWithContext' t3) ctx
  return $ TmIf' t1' t2' t3'

restoreNamesWithContext :: NamingContext -> UnNamedTerm -> Eff '[EitherDef Errors] NamedTerm
restoreNamesWithContext ctx = (`evalStateDef` ctx) . restoreNamesWithContext'

restoreNamesWithContext' :: UnNamedTerm -> Eff '[StateDef NamingContext, EitherDef Errors] NamedTerm
restoreNamesWithContext' (TmVar' n) = do
  ctx <- get
  case ctx V.!? n of
    Just (name, _) -> return $ TmVar name
    Nothing -> throwError . RestoreNamesError $ MissingVariableInNamingContextInRestoring n ctx
restoreNamesWithContext' (TmAbs' x ty t) = modify (V.cons (x, VarBind ty)) >> fmap (TmAbs x ty) (restoreNamesWithContext' t)
restoreNamesWithContext' (TmApp' t1 t2) = do
  ctx <- get
  t1' <- castEff $ evalStateDef (restoreNamesWithContext' t1) ctx
  t2' <- castEff $ evalStateDef (restoreNamesWithContext' t2) ctx
  return $ TmApp t1' t2'
restoreNamesWithContext' TmTrue' = return TmTrue
restoreNamesWithContext' TmFalse' = return TmFalse
restoreNamesWithContext' (TmIf' t1 t2 t3) = do
  ctx <- get
  t1' <- castEff $ evalStateDef (restoreNamesWithContext' t1) ctx
  t2' <- castEff $ evalStateDef (restoreNamesWithContext' t2) ctx
  t3' <- castEff $ evalStateDef (restoreNamesWithContext' t3) ctx
  return $ TmIf t1' t2' t3'

typeOf :: NamingContext -> UnNamedTerm -> Eff '[EitherDef Errors] Ty
typeOf ctx = (`evalStateDef` ctx) . typeOf'

typeOf' :: UnNamedTerm -> Eff [StateDef NamingContext, EitherDef Errors] Ty
typeOf' (TmVar' n) = do
  ctx <- get
  case ctx V.!? n of
    Just (_, VarBind ty) -> return ty
    _ -> throwError . TypingError $ MissingTypeInNamingContext (show n)
typeOf' (TmAbs' x ty t) = modify (V.cons (x, VarBind ty)) >> fmap (TyArrow ty) (typeOf' t)
typeOf' (TmApp' t1 t2) = do
  ctx <- get
  ty1 <- castEff $ evalStateDef (typeOf' t1) ctx
  ty2 <- castEff $ evalStateDef (typeOf' t2) ctx
  case ty1 of
    TyArrow ty1' ty2'
      | ty1' == ty2 -> return ty2'
    _ -> throwError . TypingError $ NotMatchedTypeTmApp t1 ty1 t2 ty2
typeOf' TmTrue' = return TyBool
typeOf' TmFalse' = return TyBool
typeOf' (TmIf' t1 t2 t3) = do
  ctx <- get
  ty1 <- castEff $ evalStateDef (typeOf' t1) ctx
  case ty1 of
    TyBool -> do
      ty2 <- castEff $ evalStateDef (typeOf' t2) ctx
      ty3 <- castEff $ evalStateDef (typeOf' t3) ctx
      if ty2 == ty3
        then return ty2
        else throwError . TypingError $ NotMatchedTypeTmIfT2T3 t2 ty2 t3 ty3
    _ -> throwError . TypingError $ NotMatchedTypeTmIfT1 t1 ty1

termShift :: DeBrujinIndex -> UnNamedTerm -> UnNamedTerm
termShift d = walk 0
  where
    walk c (TmVar' n) | n < c = TmVar' n
                      | otherwise = TmVar' (n + d)
    walk c (TmAbs' x ty t) = TmAbs' x ty $ walk (c+1) t
    walk c (TmApp' t1 t2) = TmApp' (walk c t1) (walk c t2)
    walk _ TmTrue' = TmTrue'
    walk _ TmFalse' = TmFalse'
    walk c (TmIf' t1 t2 t3) = TmIf' (walk c t1) (walk c t2) (walk c t3)

termSubst :: DeBrujinIndex -> UnNamedTerm -> UnNamedTerm -> UnNamedTerm
termSubst j s (TmVar' n) | n == j    = s
                         | otherwise = TmVar' n
termSubst j s (TmAbs' x ty t) = TmAbs' x ty $ termSubst (j + 1) (termShift 1 s) t
termSubst j s (TmApp' t1 t2) = TmApp' (termSubst j s t1) (termSubst j s t2)
termSubst _ _ TmTrue' = TmTrue'
termSubst _ _ TmFalse' = TmFalse'
termSubst j s (TmIf' t1 t2 t3) = TmIf' (termSubst j s t1) (termSubst j s t2) (termSubst j s t3)

betaReduction :: UnNamedTerm -> UnNamedTerm -> UnNamedTerm
betaReduction s t = termShift (-1) $ termSubst 0 (termShift 1 s) t

isVal :: UnNamedTerm -> Bool
isVal (TmAbs' _ _ _) = True
isVal TmTrue' = True
isVal TmFalse' = True
isVal _ = False 

eval1 :: UnNamedTerm -> Eff '[EitherDef Errors] UnNamedTerm
eval1 (TmApp' (TmAbs' _ _ t1) v2) | isVal v2 = return $ betaReduction v2 t1
eval1 (TmApp' v1 t2) | isVal v1 = TmApp' v1 <$> eval1 t2
eval1 (TmApp' t1 t2) = (`TmApp'` t2) <$> eval1 t1
eval1 (TmIf' TmTrue' t2 _) = return t2
eval1 (TmIf' TmFalse' _ t3) = return t3
eval1 (TmIf' t1 t2 t3) = do
  t1' <- eval1 t1
  return $ TmIf' t1' t2 t3
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