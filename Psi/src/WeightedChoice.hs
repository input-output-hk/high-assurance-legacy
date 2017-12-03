module WeightedChoice
    ( WeightedChoice (..)
    , weighted
    ) where

import Data.List          (foldl')
import Data.List.NonEmpty (NonEmpty (..))
import Probability

class WeightedChoice a where
    weightedChoice :: Probability -> a -> a -> a

weighted :: forall a. WeightedChoice a => NonEmpty (Rational, a) -> a
weighted ((w, a) :| [])
    | w <= 0            = error "weighted: non-positive weight with one option"
    | otherwise         = a
weighted ((w, a) :| xs) = snd $ foldl' f (w, a) xs
  where
    f :: (Rational, a) -> (Rational, a) -> (Rational, a)
    f (w', a') (w'', a'')
        | w'' < 0    = error "weighted: negative weight"
        | otherwise =
            let !w''' = w' + w''
                !p    = probability $ w' / w'''
            in  (w''', weightedChoice p a' a'')
