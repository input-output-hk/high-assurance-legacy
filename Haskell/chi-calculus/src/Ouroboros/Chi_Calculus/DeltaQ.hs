module Ouroboros.Chi_Calculus.DeltaQ
    ( Seconds
    , DeltaQ (..)
    ) where

type Seconds = Double

data DeltaQ = Uniform Seconds Seconds
    deriving Show
