{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Polynomial.Discrete
    ( Disc
    , singleton
    , foldDisc
    , foldMapDisc
    , smearDisc
    ) where

import           Data.List             (foldl')
import           Data.Map.Strict       (Map)
import qualified Data.Map.Strict       as M
import           Data.Monoid           (Sum (..))
import           Data.Polynomial.Class

newtype Disc r = Disc (Map r r)
    deriving (Eq, Ord, Show)

instance (Ord r, Num r) => Semigroup (Disc r) where
    m <> n = foldDisc (\d r p -> insertDisc r p d) m n

instance (Ord r, Num r) => Monoid (Disc r) where
    mempty = Disc M.empty

instance (Ord r, Fractional r) => Distribution r r (Disc r) where

    mass = getSum . foldMapDisc (\_ p -> Sum p)

    mean d = case foldMapDisc (\r p -> (Sum $ r * p, Sum p)) d of
        (_, Sum 0)     -> Nothing
        (Sum s, Sum p) -> Just (s / p)

    support (Disc m) = do
        ((a, _), _) <- M.minViewWithKey m
        ((b, _), _) <- M.maxViewWithKey m
        return (a, b)

    scale s = foldMapDisc (\r p -> singleton r (s * p))

    shift s = foldMapDisc (\r p -> singleton (r + s) p)

    convolve = smearDisc $ \(r, p) (s, q) -> (r + s, p * q)

    before = smearDisc $ \(r, p) (s, q) -> case compare r s of
        LT -> (r, p * q)
        EQ -> (r, p * q * p / (p + q))
        GT -> (r, 0)

    residual = smearDisc $ \(r, p) (s, q) -> case compare r s of
        LT -> (s - r, p * q)
        EQ -> (0, p * q * p / (p + q))
        GT -> (0, 0)

    endingAt t = flip before $ singleton t 1

    revTime = foldMapDisc (\r p -> singleton (-r) p)

    cdf d = getSum . foldMapDisc (\r p t -> Sum $ cdfSingleton r p t) d

foldDisc :: (a -> r -> r -> a) -> a -> Disc r -> a
foldDisc op a (Disc m) = foldl' (uncurry . op) a $ M.toList m

foldMapDisc :: Monoid m => (r -> r -> m) -> Disc r -> m
foldMapDisc op = foldDisc (\m r p -> m <> op r p) mempty

insertDisc :: (Ord r, Num r) => r -> r -> Disc r -> Disc r
insertDisc r p (Disc m) = Disc $ M.alter f r m
  where
    f Nothing
        | p == 0    = Nothing
        | otherwise = Just p
    f (Just q)    = case p + q of
        0 -> Nothing
        s -> Just s

singleton :: (Ord r, Num r) => r -> r -> Disc r
singleton r p = insertDisc r p mempty

smearDisc :: (Ord r, Num r)
          => ((r, r) -> (r, r) -> (r, r))
          -> Disc r
          -> Disc r
          -> Disc r
smearDisc op d = foldDisc f mempty
  where
    f x s q = foldDisc (g s q) x d
    g s q y r p = let (rs, pq) = op (r, p) (s, q) in insertDisc rs pq y

cdfSingleton :: (Ord r, Num r) => r -> r -> r -> r
cdfSingleton r p t
    | t < r     = 0
    | otherwise = p
