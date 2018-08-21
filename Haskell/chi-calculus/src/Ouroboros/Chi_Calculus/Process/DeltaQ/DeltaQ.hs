module Ouroboros.Chi_Calculus.Process.DeltaQ.DeltaQ
    ( Seconds
    , DeltaQ (..)
    ) where

type Seconds = Double

data DeltaQ = Uniform Seconds Seconds
    deriving Show
