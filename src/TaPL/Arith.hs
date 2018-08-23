module TaPL.Arith where

import RIO

data Ty = TyBool | TyNat deriving (Show, Eq)
data Term = TmTrue | TmFalse | TmIf Term Term Term | TmZero | TmSucc Term | TmPred Term | TmIsZero Term deriving (Show, Eq)

isNumericalVal :: Term -> Bool
isNumericalVal TmZero = True
isNumericalVal (TmSucc t) = isNumericalVal t
isNumericalVal _ = False

isVal :: Term -> Bool
isVal TmTrue = True
isVal TmFalse = True
isVal t | isNumericalVal t = True
        | otherwise        = False

eval1 :: Term -> Maybe Term
eval1 (TmIf TmTrue t2 _) = return t2
eval1 (TmIf TmFalse _ t3) = return t3
eval1 (TmIf t1 t2 t3) = do
  t1' <- eval1 t1
  return $ TmIf t1' t2 t3
eval1 (TmSucc t) = do
  t' <- eval1 t
  return $ TmSucc t'
eval1 (TmPred TmZero) = return TmZero
eval1 (TmPred (TmSucc t)) | isNumericalVal t = return t
eval1 (TmPred t) = eval1 t
eval1 (TmIsZero TmZero) = return TmTrue
eval1 (TmIsZero (TmSucc t)) | isNumericalVal t = return TmFalse
eval1 (TmIsZero t) = do
  t' <- eval1 t
  return $ TmIsZero t'
eval1 _ = Nothing

eval :: Term -> Term
eval t = case eval1 t of
  Just t' -> eval t'
  Nothing -> t

typeOf :: Term -> Maybe Ty
typeOf TmTrue = return TyBool
typeOf TmFalse = return TyBool
typeOf (TmIf t1 t2 t3) = do
  ty1 <- typeOf t1
  ty2 <- typeOf t2
  ty3 <- typeOf t3
  if ty1 == TyBool && ty2 == ty3
    then return ty2
    else Nothing
typeOf TmZero = return TyNat
typeOf (TmSucc t) = do
  ty <- typeOf t
  if ty == TyNat
    then return TyNat
    else Nothing
typeOf (TmPred t) = do
  ty <- typeOf t
  if ty == TyNat
    then return TyNat
    else Nothing
typeOf (TmIsZero t) = do
  ty <- typeOf t
  if ty == TyNat
    then return TyBool
    else Nothing