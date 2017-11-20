{-# LANGUAGE TypeFamilies #-}

module Psi
    ( Psi (..)
    ) where

import Prelude hiding (repeat)

class Psi p where
  type Chan p  :: * -> *
  type Value p :: * -> *
  done   :: p
  nu     :: (Chan p a -> p) -> p
  inp    :: Chan p a -> (Value p a -> p) -> p
  out    :: Chan p a -> Value p a -> p -> p
  fork   :: p -> p -> p
  repeat :: p -> p
