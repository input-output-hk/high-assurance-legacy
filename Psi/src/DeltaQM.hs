module DeltaQM
    ( DeltaQM (..)
    ) where

import Control.Applicative
import Control.Monad
import Distribution
import MonadDeltaQ

data DeltaQM d a =
      Bottom
    | Tangible Rational [(a, Rational, d)]
    deriving Show

instance Distribution d => Functor (DeltaQM d) where
    fmap = liftM

instance Distribution d => Applicative (DeltaQM d) where
    pure  = return
    (<*>) = ap

instance Distribution d => Monad (DeltaQM d) where
    return a             = Tangible 1 [(a, 1, dirac 0)]

    Bottom        >>= _ = Bottom
    Tangible t xs >>= f = undefined

instance Distribution d => MonadDeltaQ (DeltaQM d) d where
    vitiate d = Tangible 1 [((), 1, d)]

instance Distribution d => Alternative (DeltaQM d) where
    empty = Bottom
    (<|>) = ftf

instance Distribution d => MonadPlus (DeltaQM d)
