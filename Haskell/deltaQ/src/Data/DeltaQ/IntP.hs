module Data.DeltaQ.IntP
    ( IntP (getIntP)
    , intP
    ) where

import Data.DeltaQ.Core

newtype IntP = IntP {getIntP :: Int}
    deriving (Eq, Ord)

instance Show IntP where
    show (IntP n) = show n

intP :: Int -> IntP
intP = IntP . max 0

instance Semigroup IntP where
    IntP m <> IntP n = IntP $ m + n

instance Monoid IntP where
    mempty = intP 0

instance Time IntP where

instance Enum IntP where
    toEnum = intP
    fromEnum = getIntP
