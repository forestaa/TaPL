{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SString (SString, pack) where

import RIO
import qualified RIO.Text as Text

newtype SString = SString Text.Text deriving (Eq, Ord, IsString)
instance Show SString where
  show (SString s) = Text.unpack s
instance Semigroup SString where
  SString s1 <> SString s2 = SString (s1 <> s2)
instance Monoid SString where
  mempty = SString ""
pack :: String -> SString
pack = SString . Text.pack
