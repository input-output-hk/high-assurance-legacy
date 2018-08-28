{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Data.DeltaQ.Core
    ( DeltaQ (..)
    ) where

import Data.DeltaQ.Probability

class Monoid b => DeltaQ a b | b -> a where
    before   :: b -> b -> Prob a
    residuum :: b -> b -> Maybe b
