module Probability
    ( Probability
    , probability
    ) where

newtype Probability = Probability Rational
    deriving Show

probability :: Rational -> Probability
probability p
    | p < 0 || p > 1 = error "probability: must be in [0,1]"
    | otherwise      = Probability p
