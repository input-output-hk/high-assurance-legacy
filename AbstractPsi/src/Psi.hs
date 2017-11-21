module Psi
    ( Psi (..)
    ) where

class Psi p where
  type Chan p  :: * -> *
  type Value p :: * -> *
  done   :: p
  nu     :: (Chan p a -> p) -> p
  inp    :: Chan p a -> (Value p a -> p) -> p
  out    :: Chan p a -> Value p a -> p -> p
  fork   :: p -> p -> p
