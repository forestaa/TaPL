{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies  #-}

module MapLeftEff where

import RIO (($))
import Control.Monad.Skeleton (hoistSkeleton)
import Data.Bifunctor (first)
import Data.Extensible.Effect
import Data.Extensible.Effect.Default
import Data.Extensible.Internal

mapHeadEff :: (forall x. s x -> t x) -> Eff ((k >: s) ': xs) a -> Eff ((k' >: t) ': xs) a
mapHeadEff f = hoistSkeleton $ \(Instruction i t) -> leadership i 
  (\Refl -> Instruction here $ f t) 
  (\j -> Instruction (navNext j) t)

mapLeftEff :: (e -> e') -> Eff ((k >: EitherEff e) ': xs) a -> Eff ((k >: EitherEff e') ': xs) a
mapLeftEff f = mapHeadEff (first f)

mapLeftDef :: (e -> e') -> Eff (EitherDef e ': xs) a -> Eff (EitherDef e' ': xs) a
mapLeftDef = mapLeftEff