module DeltaQM
    ( DeltaQM (..)
    , tangible
    ) where

import Control.Applicative
import Control.Monad
import Distribution
import MonadDeltaQ
import Probability
import WeightedChoice

newtype DeltaQM d a = DeltaQM [(a, Probability, d)]
    deriving Show

tangible :: DeltaQM d a -> Probability
tangible (DeltaQM xs) = sum [p | (_, p, _) <- xs]

instance WeightedChoice (DeltaQM d a) where
    weightedChoice 0 _            x            = x
    weightedChoice 1 x            _            = x
    weightedChoice p (DeltaQM xs) (DeltaQM ys) =
        let xs' = [(a, q * p, d)       | (a, q, d) <- xs]
            ys' = [(a, q * (1 - p), d) | (a, q, d) <- ys]
        in  DeltaQM $ xs' ++ ys'

instance Distribution d => Functor (DeltaQM d) where
    fmap = liftM

instance Distribution d => Applicative (DeltaQM d) where
    pure  = return
    (<*>) = ap

instance Distribution d => Monad (DeltaQM d) where
    return a         = DeltaQM [(a, 1, dirac 0)]
    DeltaQM xs >>= f = undefined

instance Distribution d => MonadDeltaQ (DeltaQM d) d where
    vitiate d = DeltaQM [((), 1, d)]

instance Distribution d => Alternative (DeltaQM d) where
    empty = DeltaQM []
    (<|>) = ftf

instance Distribution d => MonadPlus (DeltaQM d)
