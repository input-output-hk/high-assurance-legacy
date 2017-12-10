{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : WeightedChoice
Description : probabilistic choice
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module defines class @'WeightedChoice'@ for types
which admit probabilistic choice.
-}

module WeightedChoice
    ( WeightedChoice (..)
    , weighted
    ) where

import Data.List          (foldl')
import Data.List.NonEmpty (NonEmpty (..))
import Probability

class WeightedChoice a where

    -- | @'weightedChoice' p x y@ chooses between two options
    -- @x@ and @y@, picking @x@ with probability @p@ and @y@ with probability
    -- @1-p@.
    --
    -- The following equations should hold:
    --
    -- > weightedChoice 1 x y = x
    -- > weightedChoice 0 x y = y
    weightedChoice :: Probability -> a -> a -> a

-- | Generalization of @'weightedChoice'@ to non-empty lists of options,
-- given by weight-value pairs. The values will be chosen with probability
-- proportional to their weight. All weights must be non-negative, and at least
-- one weight must be positive.
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
