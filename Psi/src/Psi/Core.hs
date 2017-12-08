{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Psi.Core
Description : PHOAS representation of the psi-calculus
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module gives a PHOAS representation of a version
of the psi-calculus.
-}

module Psi.Core
    ( Psi (..)
    ) where

import Distribution
import Probability

-- | Class for psi-calculus processes @p@.
class Psi p where

    -- | Type constructor for channels.
    type Chan p :: * -> *

    -- | Type constructor for values.
    type Value p :: * -> *

    -- | The type of globally visible observations.
    type Observation p :: *

    -- | The process that does nothing and immediately stops.
    done    :: p

    -- | Channel creation.
    nu      :: (Chan p a -> p) -> p

    -- | Waiting for input on a channel.
    inp     :: Chan p a -> (Value p a -> p) -> p

    -- | Outputting a value on a channel.
    out     :: Chan p a -> Value p a -> p -> p

    -- | Forking a parallel process.
    fork    :: p -> p -> p

    -- | Making a (globally visible) observation.
    observe :: Observation p -> p -> p

    -- | Delaying the process.
    delay   :: DTime -> p -> p

    -- | Making a probabilistic choice between two processes.
    choice  :: Probability -> p -> p -> p
