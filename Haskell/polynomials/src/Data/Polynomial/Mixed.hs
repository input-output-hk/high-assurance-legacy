{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.Polynomial.Mixed
    ( QAlg (..)
    , evalPW
    , foldDisc
    , foldMapDisc
    , Mixed (..)
    , exactMixed
    , uniformMixed
    ) where

import Data.Polynomial.Class
import Data.Polynomial.Discrete
import Data.Polynomial.Piecewise

data Mixed r = Mixed (Disc r) (Piecewise r)
    deriving (Show, Eq, Ord)

instance (Ord r, QAlg r) => Semigroup (Mixed r) where
    Mixed d ps <> Mixed e qs = Mixed (d <> e) (ps <> qs)

instance (Ord r, QAlg r) => Monoid (Mixed r) where
    mempty = Mixed mempty mempty

instance (Ord r, QAlg r, Fractional r) => Distribution r r (Mixed r) where

    mass (Mixed d ps) = mass d + mass ps

    mean (Mixed d ps) = case (mean d, mean ps) of
        (Nothing, Nothing) -> Nothing
        (m, Nothing)       -> m
        (Nothing, m)       -> m
        (Just m, Just m')  ->
            let p  = mass d
                p' = mass ps
            in  Just $ (p * m + p' * m') / (p + p')

    support (Mixed d ps) = case (support d, support ps) of
        (Nothing, Nothing)           -> Nothing
        (s, Nothing)                 -> s
        (Nothing, s)                 -> s
        (Just (a, b), Just (a', b')) -> Just (min a a', max b b')

    convolve (Mixed d ps) (Mixed e qs) =
        Mixed (convolve d e) (convolve ps qs <> f d qs <> f e ps)
      where
        f :: Disc r -> Piecewise r -> Piecewise r
        f d' x = foldMapDisc (\r p -> scale p $ shift r x) d'

    scale r (Mixed d ps) = Mixed (scale r d) (scale r ps)

    shift r (Mixed d ps) = Mixed (shift r d) (shift r ps)

    before (Mixed d ps) (Mixed e qs) =
        Mixed (before d e   <> foldMapDisc f d)
              (before ps qs <> foldMapDisc g e)
      where
        f r p = scale p $ singleton r $ mass $ startingAt r qs
        g r p = scale p $ endingAt r ps

    revTime (Mixed d ps) = Mixed (revTime d) (revTime ps)

    endingAt t (Mixed d ps) = Mixed (endingAt t d) (endingAt t ps)

    residual (Mixed d ps) (Mixed e qs) =
        Mixed (residual d e)
              (residual ps qs <> foldMapDisc f d <> foldMapDisc g e)
      where
        f r p = scale p $ shift (-r) $ startingAt r qs
        g r p = scale p $ shift r $ revTime $ endingAt r ps

    cdf (Mixed d ps) t = cdf d t + cdf ps t

instance (Ord r, QAlg r, Fractional r) => Num (Mixed r) where
    (+) = (<>)
    (*) = convolve
    negate = (* fromQ (-1))
    fromInteger = fromQ . fromInteger
    abs = const $ error "Mixed distributions do not have an absolute value."
    signum = const $ error "Mixed distributions do not have a sign."

instance (Ord r, QAlg r, Fractional r) => QAlg (Mixed r) where
    fromQ q = Mixed (singleton 0 $ fromQ q) mempty

exactMixed :: (Ord r, QAlg r) => r -> Mixed r
exactMixed r = Mixed (singleton r 1) mempty

uniformMixed :: (Ord r, QAlg r, Fractional r) => r -> r -> Mixed r
uniformMixed a b = Mixed mempty $ uniformPW a b


