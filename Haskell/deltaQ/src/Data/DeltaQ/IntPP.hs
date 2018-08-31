module Data.DeltaQ.IntPP
    ( IntPP (..)
    , subPP
    ) where

import Data.DeltaQ.IntP

data IntPP = Finite !IntP | Infinity
    deriving (Eq, Ord)

instance Show IntPP where
    show (Finite n) = show n
    show Infinity   = "∞"

instance Semigroup IntPP where
    Infinity <> _        = Infinity
    _        <> Infinity = Infinity
    Finite m <> Finite n = Finite $ m <> n

instance Monoid IntPP where
    mempty = Finite mempty

subPP :: IntPP -> IntPP -> IntPP
Finite m `subPP` Finite n = Finite $ m `subP` n
Finite _ `subPP` Infinity = mempty
Infinity `subPP` _        = Infinity
