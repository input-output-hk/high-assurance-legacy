module Psi.Examples
    ( pingPong
    ) where

import Data.Functor.Identity
import Psi.Core

pingPong :: (Psi p, Value p ~ Identity, Observation p ~ String) => p
pingPong = nu $ \c -> fork
    (inp c $ \(Identity s) -> observe s $ delay 1 $ out c (Identity "pong") done)
    (delay 1 $ out c (Identity "ping") $ inp c $ \(Identity s) -> observe s done)
