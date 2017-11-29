module Probability
    ( Probability
    , probability
    ) where

newtype Probability = Probability Rational
    deriving (Show, Eq, Ord)

probability :: Rational -> Probability
probability p
    | p < 0 || p > 1 = error "probability: must be in [0,1]"
    | otherwise      = Probability p

instance Num Probability where
    Probability x + Probability y = probability (x + y)
    Probability x * Probability y = probability (x * y)
    Probability x - Probability y = probability (x - y)
    abs = id
    signum (Probability 0) = 0
    signum (Probability _) = 1
    fromInteger = probability . fromInteger
