module Data.DeltaQ.IntP
    ( IntP (..)
    , subP
    ) where

data IntP = Finite !Int | Infinity
    deriving (Eq, Ord)

instance Show IntP where
    show (Finite n) = show n
    show Infinity   = "∞"

instance Semigroup IntP where
    Infinity <> _        = Infinity
    _        <> Infinity = Infinity
    Finite m <> Finite n = Finite $ m + n

instance Monoid IntP where
    mempty = Finite 0

subP :: IntP -> Int -> IntP
subP (Finite m) n = Finite $ m - n
subP Infinity   _ = Infinity
