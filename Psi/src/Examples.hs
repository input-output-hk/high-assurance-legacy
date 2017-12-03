module Examples
    ( noRetry
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

latency :: DTime
latency = weighted $ (1, dirac 1) :| [(1, dirac 2), (1, dirac 3)]

step :: DeltaQM ()
step = weightedChoice 0.9 (vitiate latency) empty

hops, tries :: Int
hops = 10
tries = 3

noRetry :: DeltaQM ()
noRetry = replicateM_ hops step

globalRetry :: DeltaQM ()
globalRetry = retryMany noRetry $ replicate tries $ dirac 30

localRetry :: DeltaQM ()
localRetry =
    let step' = compact $ retryMany step $ replicate tries $ dirac 3
    in  replicateM_ hops step'
