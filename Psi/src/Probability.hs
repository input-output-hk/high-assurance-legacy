{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Probability
Description : probabilities
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module defines type @'Probability'@ for the representation of probabilities.
-}

module Probability
    ( Probability
    , probability
    , fromProbability
    , probToDouble
    ) where

-- | Abstract type for the representation of probabilities.
newtype Probability = Probability Rational
    deriving (Show, Eq, Ord)

-- | Smart constructor for a @'Probability'@. The @'Rational'@ argument must be
-- in [0,1].
probability :: Rational -> Probability
probability p
    | p < 0 || p > 1 = error $ "probability: must be in [0,1], but is " ++ show p ++ " (" ++ show (fromRational p :: Double) ++ ")"
    | otherwise      = Probability p

instance Num Probability where
    Probability x + Probability y = probability (x + y)
    Probability x * Probability y = probability (x * y)
    Probability x - Probability y = probability (x - y)
    abs = id
    signum (Probability 0) = 0
    signum (Probability _) = 1
    fromInteger = probability . fromInteger

-- | Converts a @'Probability'@ to a @'Rational'@ number. The result is
-- guaranteed to be in [0,1].
fromProbability :: Probability -> Rational
fromProbability (Probability p) = p

instance Fractional Probability where
    fromRational                      = probability
    (Probability p) / (Probability q) = probability $ p / q

-- | Converts a @'Probability'@ to a @'Double'@. The result is
-- guaranteed to be in [0,1].
probToDouble :: Probability -> Double
probToDouble = fromRational . fromProbability
