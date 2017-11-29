module WeightedChoice
    ( WeightedChoice (..)
    , weighted
    ) where

import Data.List.NonEmpty
import Probability

class WeightedChoice a where
    weightedChoice :: Probability -> a -> a -> a

weighted :: WeightedChoice a => NonEmpty (Rational, a) -> a
weighted ((w, a) :| [])
    | w < 0                          = error "weighted: negative weight"
    | w == 0                         = error "weighted: at least one weight must be positive"
    | otherwise                      = a
weighted ((w, a) :| ((w', a') : xs))
    | w < 0                          = error "weighted: negative weight"
    | otherwise                      =
        let ws = w + w' + sum (fst <$> xs)
            b  = weighted $ (w', a') :| xs
            p  = probability $ w / ws
        in  weightedChoice p a b
