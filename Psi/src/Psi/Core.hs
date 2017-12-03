module Psi.Core
    ( Psi (..)
    ) where

import Numeric.Natural

class Psi p where
    type Chan p :: * -> *
    type Value p :: * -> *
    type Observation p :: *
    done    :: p
    nu      :: (Chan p a -> p) -> p
    inp     :: Chan p a -> (Value p a -> p) -> p
    out     :: Chan p a -> Value p a -> p -> p
    fork    :: p -> p -> p
    observe :: Observation p -> p -> p 
    delay   :: Natural -> p -> p
