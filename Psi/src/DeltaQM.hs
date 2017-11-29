module DeltaQM
    ( DeltaQM (..)
    ) where

import Control.Applicative
import Control.Monad
import Distribution
import MonadDeltaQ

data DeltaQM d a = DeltaQM Rational [(a, Rational, d)]
    deriving Show

instance Distribution d => Functor (DeltaQM d) where
    fmap = liftM

instance Distribution d => Applicative (DeltaQM d) where
    pure  = return
    (<*>) = ap

instance Distribution d => Monad (DeltaQM d) where
    return a = DeltaQM 1 [(a, 1, dirac 0)]

instance Distribution d => MonadDeltaQ (DeltaQM d) d where
    vitiate d = DeltaQM 1 [((), 1, d)]

instance Distribution d => Alternative (DeltaQM d) where
    empty = DeltaQM 0 []
    (<|>) = ftf

instance Distribution d => MonadPlus (DeltaQM d)
