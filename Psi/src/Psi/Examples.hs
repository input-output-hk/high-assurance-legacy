module Psi.Examples
    ( pingPong
    , noRetryPsi
    ) where

import Data.Functor.Identity
import Data.List.NonEmpty
import Distribution
import Psi.Core
import WeightedChoice

pingPong :: (Psi p, Value p ~ Identity, Observation p ~ String) => p
pingPong = nu $ \c -> fork
    (inp c $ \(Identity s) -> observe s $ delay (dirac 1) $ out c (Identity "pong") done)
    (delay (dirac 1) $ out c (Identity "ping") $ inp c $ \(Identity s) -> observe s done)

bottom :: Psi p => p
bottom = delay (dirac 1000000) bottom

send :: Psi p => Chan p a -> Value p a -> p -> p
send c a p = choice 0.9
    (delay (weighted $ (1, dirac 1) :| [(1, dirac 2), (1, dirac 3)]) $ out c a p)
    bottom

hops :: Int
hops = 10

noRetryPsi :: forall p. (Psi p, Value p ~ Identity, Observation p ~ String) => p
noRetryPsi = nu $ \c -> fork (go 1 c) $ send c (Identity ()) done
  where
    go :: Int -> Chan p () -> p
    go i c = inp c $ \_ -> if i == hops
        then observe "Done" done
        else nu $ \d -> fork (go (i + 1) d) $ send d (Identity ()) done
