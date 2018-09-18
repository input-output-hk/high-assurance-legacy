{-# LANGUAGE ScopedTypeVariables #-}

module Data.Polynomial.Mixed
    ( Mixed (..)
    , convolveMixed
    , exactMixed
    , uniformMixed
    ) where

import Data.Polynomial.Discrete
import Data.Polynomial.Piecewise

data Mixed r = Mixed (Disc r) (Piecewise r)
    deriving (Show, Eq, Ord)

instance (Ord r, QAlg r) => Semigroup (Mixed r) where
    Mixed d ps <> Mixed e qs = Mixed (d <> e) (ps <> qs)

instance (Ord r, QAlg r) => Monoid (Mixed r) where
    mempty = Mixed mempty mempty

convolveMixed :: forall r. (Ord r, QAlg r) => Mixed r -> Mixed r -> Mixed r
convolveMixed (Mixed d ps) (Mixed e qs) =
    Mixed (convolveDisc d e) (convolvePW ps qs <> f d qs <> f e ps)
  where
    f :: Disc r -> Piecewise r -> Piecewise r
    f d' = foldMap (g d') . pieces

    g :: Disc r -> Piece r -> Piecewise r
    g d' x = foldMapDisc (\r p -> pw [scalePiece p $ shiftPiece r x]) d'

instance (Ord r, QAlg r) => Num (Mixed r) where
    (+) = (<>)
    (*) = convolveMixed
    negate = (* fromQ (-1))
    fromInteger = fromQ . fromInteger
    abs = const $ error "Mixed distributions do not have an absolute value."
    signum = const $ error "Mixed distributions do not have a sign."

instance (Ord r, QAlg r) => QAlg (Mixed r) where
    fromQ q = Mixed (singleton 0 $ fromQ q) mempty

exactMixed :: (Ord r, Num r) => r -> Mixed r
exactMixed r = Mixed (singleton r 1) noPiece

uniformMixed :: (Ord r, Fractional r) => r -> r -> Mixed r
uniformMixed a b = Mixed emptyDisc $ uniformPW a b
