module Psi
    ( Psi (..)
    , IChan (..)
    ) where

import Data.Functor.Identity (Identity (..))

class Psi p where
  type Chan p  :: * -> *
  type Value p :: * -> *
  done   :: p
  nu     :: (Chan p a -> p) -> p
  inp    :: Chan p a -> (Value p a -> p) -> p
  out    :: Chan p a -> Value p a -> p -> p
  fork   :: p -> p -> p

newtype IChan a = IChan Int

data IPsi where
    Done :: IPsi
    Nu   :: (IChan a -> IPsi) -> IPsi
    Inp  :: IChan a -> (a -> IPsi) -> IPsi
    Out  :: IChan a -> a -> IPsi -> IPsi
    Fork :: IPsi -> IPsi -> IPsi

instance Psi IPsi where
    type Chan IPsi  = IChan
    type Value IPsi = Identity
    done    = Done
    nu      = Nu
    inp c k = Inp c (k . Identity)
    out c   = Out c . runIdentity
    fork    = Fork
