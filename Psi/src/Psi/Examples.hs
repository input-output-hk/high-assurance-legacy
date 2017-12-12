{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Psi.Examples
Description : examples of psi-calculus processes
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module gives some examples of abstract psi-calculus processes.
-}

module Psi.Examples
    ( pingPong
    , bottom
    , send
    , hops
    , noRetryPsi
    ) where

import Data.Functor.Identity
import Data.List.NonEmpty
import Distribution
import Psi.Core
import WeightedChoice

-- | Simple example of a psi-calculus process: A channel is created and shared
-- between two processes. One process sends a "ping" to the other process, which
-- repsonds by answering with "pong".
pingPong :: (Psi p, Value p ~ Identity, Observation p ~ String) => p
pingPong = nu $ \c -> fork
    (inp c $ \(Identity s) -> observe s $ delay (dirac 1) $ out c (Identity "pong") done)
    (delay (dirac 1) $ out c (Identity "ping") $ inp c $ \(Identity s) -> observe s done)

-- | The "bottom" process that never finishes, represented as a repeated delay
-- by one second.
bottom :: Psi p => p
bottom = delay (dirac 1000000) bottom

-- | Combinator for a process that sends with latency and possible failure on a
-- channel. Sending will succeed with a probability of 90%, and in that case
-- will take one, two or three seconds with equal probability.
send :: Psi p
     => Chan p a   -- ^ channel to send on
     -> Value p a  -- ^ value to send
     -> p          -- ^ continuation
     -> p
send c a p = choice 0.9
    (delay (weighted $ (1, dirac 1) :| [(1, dirac 2), (1, dirac 3)]) $ out c a p)
    bottom

-- | The number of hops.
hops :: Int
hops = 10

-- | The psi-calculus process that tries @'hops'@ sending operations in
-- sequence, where each sending has latency and can fail (as expressed by
-- @'send'@).
noRetryPsi :: forall p. (Psi p, Value p ~ Identity, Observation p ~ String) => p
noRetryPsi = nu $ \c -> fork (go 1 c) $ send c (Identity ()) done
  where
    go :: Int -> Chan p () -> p
    go i c = inp c $ \_ -> if i == hops
        then observe "Done" done
        else nu $ \d -> fork (go (i + 1) d) $ send d (Identity ()) done
