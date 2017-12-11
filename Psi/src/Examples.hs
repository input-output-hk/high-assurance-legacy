{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Examples
Description : example @MonadDeltaQ@-computations
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module contains examples of computations in @'MonadDeltaQ'@.
-}

module Examples
    ( latency
    , step
    , hops
    , tries
    , noRetry
    , globalRetry
    , localRetry
    ) where

import Control.Applicative
import Control.Monad
import Data.List.NonEmpty  (NonEmpty (..))
import DeltaQM
import Distribution
import MonadDeltaQ
import WeightedChoice

-- | Probabilistic time, approximating a uniform distribution over [1,3]
-- by the discrete distribution of picking one, two or three
-- seconds with equal probability.
latency :: DTime
latency = weighted $ (1, dirac 1) :| [(1, dirac 2), (1, dirac 3)]

-- | Probabilistic time with intangible mass: Can fail with a probability of
-- 10%, will have distribution @'latency'@ with probability 90%.
step :: DeltaQM ()
step = weightedChoice 0.9 (vitiate latency) empty

-- | The number of hops.
hops :: Int
hops = 10

-- | The number of tries.
tries :: Int
tries = 3

-- | Performs @'hops'@ @'step'@s in sequence, no retry.
noRetry :: DeltaQM ()
noRetry = replicateM_ hops step

-- | Tries up to @'tries'@ times to perform @'hops'@ @'step'@s in sequence.
globalRetry :: DeltaQM ()
globalRetry = retryMany noRetry $ replicate tries $ dirac 30

-- | Performs @'hops'@ steps with local retry in sequence, i.e. tries each @'step'@
-- up to @'tries'@ times.
localRetry :: DeltaQM ()
localRetry =
    let step' = compact $ retryMany step $ replicate tries $ dirac 3
    in  replicateM_ hops step'
