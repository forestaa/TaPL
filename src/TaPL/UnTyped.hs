{-# language DataKinds #-}

module TaPL.UnTyped where

import Control.Monad.Error.Class
import Control.Monad.State.Strict

import Data.Extensible.Effect
import Data.Extensible.Effect.Default
import qualified Data.Set as S
import qualified Data.List as L

type DeBrujinIndex = Int
data NamedTerm = TmVar String | TmAbs String NamedTerm | TmApp NamedTerm NamedTerm deriving (Show)
data UnNamedTerm = TmVar' DeBrujinIndex | TmAbs' String UnNamedTerm | TmApp' UnNamedTerm UnNamedTerm deriving (Show)
type NamingContext = [String]

freeVariable :: NamedTerm -> S.Set String
freeVariable = leaveEff . (`evalStateDef` S.empty) . freeVariable'

freeVariable' :: NamedTerm -> Eff '[StateDef (S.Set String)] (S.Set String)
freeVariable' (TmVar x) = do
  b <- gets (S.member x)
  if b
    then return S.empty 
    else return $ S.singleton x 
freeVariable' (TmAbs x t) = modify (S.insert x) >> freeVariable' t
freeVariable' (TmApp t1 t2) = do
  bounds <- get
  vs1 <- castEff $ evalStateDef (freeVariable' t1) bounds
  vs2 <- castEff $ evalStateDef (freeVariable' t2) bounds
  return $ S.union vs1 vs2

removeNames :: NamedTerm -> Either String UnNamedTerm
removeNames t = removeNamesWithContext (S.toList $ freeVariable t) t

removeNamesWithContext :: NamingContext -> NamedTerm -> Either String UnNamedTerm
removeNamesWithContext ctx = leaveEff . runEitherDef . (`evalStateDef` ctx) . removeNamesWithContext'

removeNamesWithContext' :: NamedTerm -> Eff '[StateDef NamingContext, EitherDef String] UnNamedTerm
removeNamesWithContext' (TmVar x) = do
  maybei <- gets (L.elemIndex x)
  case maybei of
    Just i -> return $ TmVar' i
    Nothing -> throwError $ "missing " ++ x
removeNamesWithContext' (TmAbs x t) = modify ((:) x) >> fmap (TmAbs' x) (removeNamesWithContext' t)
removeNamesWithContext' (TmApp t1 t2) = do
  ctx <- get
  t1' <- castEff $ evalStateDef (removeNamesWithContext' t1) ctx
  t2' <- castEff $ evalStateDef (removeNamesWithContext' t2) ctx
  return $ TmApp' t1' t2'

restoreNamesWithContext :: NamingContext -> UnNamedTerm -> Either String NamedTerm
restoreNamesWithContext ctx = leaveEff . runEitherDef . (`evalStateDef` ctx) . restoreNamesWithContext'

restoreNamesWithContext' :: UnNamedTerm -> Eff '[StateDef NamingContext, EitherDef String] NamedTerm
restoreNamesWithContext' (TmVar' n) = gets (TmVar . (!! n))
restoreNamesWithContext' (TmAbs' x t) = modify ((:) x) >> fmap (TmAbs x) (restoreNamesWithContext' t)
restoreNamesWithContext' (TmApp' t1 t2) = do
  ctx <- get
  t1' <- castEff $ evalStateDef (restoreNamesWithContext' t1) ctx
  t2' <- castEff $ evalStateDef (restoreNamesWithContext' t2) ctx
  return $ TmApp t1' t2'

termShift :: DeBrujinIndex -> UnNamedTerm -> UnNamedTerm
termShift d = walk 0
  where
    walk c (TmVar' n) | n < c = TmVar' n
                      | otherwise = TmVar' (n + d)
    walk c (TmAbs' x t) = TmAbs' x $ walk (c+1) t
    walk c (TmApp' t1 t2) = TmApp' (walk c t1) (walk c t2)

termSubst :: DeBrujinIndex -> UnNamedTerm -> UnNamedTerm -> UnNamedTerm
termSubst j s (TmVar' n) | n == j    = s
                         | otherwise = TmVar' n
termSubst j s (TmAbs' x t) = TmAbs' x $ termSubst (succ j) (termShift 1 s) t
termSubst j s (TmApp' t1 t2) = TmApp' (termSubst j s t1) (termSubst j s t2)

betaReduction :: UnNamedTerm -> UnNamedTerm -> UnNamedTerm
betaReduction s t = termShift (-1) $ termSubst 0 (termShift 1 s) t

isVal :: UnNamedTerm -> Bool
isVal (TmAbs' _ _) = True
isVal _            = False

data NoRuleApplies = NoRuleApplies
eval1 :: UnNamedTerm -> Either NoRuleApplies UnNamedTerm
eval1 (TmApp' (TmAbs' _ t1) v2@(TmAbs' _ _)) = return $ betaReduction v2 t1
eval1 (TmApp' v1@(TmAbs' _ _) t2) = TmApp' v1 <$> eval1 t2
eval1 (TmApp' t1 t2) = (`TmApp'` t2) <$> eval1 t1
eval1 _ = throwError NoRuleApplies

eval' :: UnNamedTerm -> UnNamedTerm
eval' t = case eval1 t of
  Right t'           -> eval' t'
  Left NoRuleApplies -> t

eval :: NamedTerm -> Either String NamedTerm
eval t = do
  let fv = S.toList $ freeVariable t
  t' <- removeNamesWithContext fv t
  restoreNamesWithContext fv (eval' t')
