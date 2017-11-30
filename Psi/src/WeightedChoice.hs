module WeightedChoice
    ( WeightedChoice (..)
    , weighted
    ) where

import Probability

class WeightedChoice a where
    neutral        :: a
    weightedChoice :: Probability -> a -> a -> a

weighted :: WeightedChoice a => [(Rational, a)] -> a
weighted []                          = neutral
weighted [(w, a)]
    | w < 0                          = error "weighted: negative weight"
    | w == 0                         = neutral
    | otherwise                      = a
weighted ((w, a) : xs)
    | w < 0                          = error "weighted: negative weight"
    | otherwise                      =
        let ws = w + sum (fst <$> xs)
            b  = weighted xs
            p  = probability $ w / ws
        in  weightedChoice p a b
