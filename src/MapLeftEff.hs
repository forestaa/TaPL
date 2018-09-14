{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies  #-}

module MapLeftEff where

import RIO (($))
import Control.Monad.Skeleton (hoistSkeleton)
import Data.Bifunctor (first)
import Data.Extensible.Effect
import Data.Extensible.Effect.Default
import Data.Extensible.Internal


mapLeftEff :: (e -> e') -> Eff ((k >: EitherEff e) ': xs) a -> Eff ((k >: EitherEff e') ': xs) a
mapLeftEff f = hoistSkeleton $ \(Instruction i t) -> leadership i 
  (\Refl -> Instruction here $ first f t) 
  (\j -> Instruction (navNext j) t)

mapLeftDef :: (e -> e') -> Eff (EitherDef e ': xs) a -> Eff (EitherDef e' ': xs) a
mapLeftDef = mapLeftEff