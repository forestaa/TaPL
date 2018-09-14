{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

module TaPL.NameLess where

import RIO

import Control.Monad.Error.Class
import Data.Extensible
import Data.Extensible.Effect.Default

import SString

type DeBrujinIndex = Int

type family Named (a :: Bool) = r | r -> a where
  Named 'True  = SString
  Named 'False = DeBrujinIndex
type NameLessVariable = Named 'False

type family Not (a :: Bool) where
  Not 'True = 'False
  Not 'False = 'True

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
data NameLessErrors =
    UnNameError UnNameError
  | RestoreNameError RestoreNameError
  deriving (Eq)
instance Show NameLessErrors where
  show (UnNameError e) = "UnName Error: " ++ show e
  show (RestoreNameError e) = "RestoreName Error: " ++ show e


class FindVar (f :: Bool -> *) (a :: Bool) where
  findvar :: Proxy f -> NamingContext -> Named a -> Maybe (Named (Not a))
class FindVar f a => NameLess (f :: Bool -> *) a where
  nameless :: f a -> Eff [EitherDef (NamingContextError a), ReaderDef NamingContext] (f (Not a))
type UnNameError = NamingContextError 'True
unName :: NameLess f 'True => f 'True -> Eff '[EitherDef UnNameError, ReaderDef NamingContext] (f 'False)
unName = nameless
type RestoreNameError = NamingContextError 'False
restoreName :: NameLess f 'False => f 'False -> Eff '[EitherDef RestoreNameError, ReaderDef NamingContext] (f 'True)
restoreName = nameless

leaveUnName :: NameLess f 'True => NamingContext -> f 'True -> Either UnNameError (f 'False)
leaveUnName ctx t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ unName t
leaveRestoreName :: NameLess f 'False => NamingContext -> f 'False -> Either RestoreNameError (f 'True)
leaveRestoreName ctx t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ restoreName t
leaveUnRestoreName :: (NameLess f 'True, NameLess f 'False) => NamingContext -> f 'True -> Either NameLessErrors (f 'True)
leaveUnRestoreName ctx t = leaveEff . (`runReaderDef` ctx) . runEitherDef $ do
  t' <- mapEitherDef UnNameError $ unName t
  mapEitherDef RestoreNameError $ restoreName t'
  where
    mapEitherDef :: (e -> e') -> Eff '[EitherDef e, ReaderDef r] a -> Eff '[EitherDef e', ReaderDef r] a
    mapEitherDef f m = do
      ret <- castEff $ runEitherDef m
      case ret of
        Right a -> return a
        Left e -> throwError $ f e
-- leaveUnRestoreName ctx t = do
--   t' <- mapLeft UnNameError $ leaveUnName ctx t
--   mapLeft RestoreNameError $ leaveRestoreName ctx t'

