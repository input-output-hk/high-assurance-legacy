module Data.Polynomial.Discrete
    ( Disc
    , emptyDisc
    , singleton
    , intDisc
    , convolveDisc
    , beforeDisc
    , foldDisc
    , foldMapDisc
    , smearDisc
    , scaleDisc
    ) where

import           Data.List       (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

newtype Disc r = Disc (Map r r)
    deriving (Eq, Ord, Show)

emptyDisc :: Disc r
emptyDisc = Disc M.empty

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
singleton r p = insertDisc r p emptyDisc

instance (Ord r, Num r) => Semigroup (Disc r) where
    m <> n = foldDisc (\d r p -> insertDisc r p d) m n

instance (Ord r, Num r) => Monoid (Disc r) where
    mempty = emptyDisc

intDisc :: Num r => Disc r -> r
intDisc = foldDisc (\acc r p -> acc + r * p) 0

smearDisc :: (Ord r, Num r)
          => ((r, r) -> (r, r) -> (r, r))
          -> Disc r
          -> Disc r
          -> Disc r
smearDisc op d = foldDisc f emptyDisc
  where
    f x s q = foldDisc (g s q) x d
    g s q y r p = let (rs, pq) = op (r, p) (s, q) in insertDisc rs pq y

convolveDisc :: (Ord r, Num r) => Disc r -> Disc r -> Disc r
convolveDisc = smearDisc $ \(r, p) (s, q) -> (r + s, p * q)

beforeDisc :: (Ord r, Fractional r) => Disc r -> Disc r -> Disc r
beforeDisc = smearDisc $ \(r, p) (s, q) -> case compare r s of
    LT -> (r, p * q)
    EQ -> (r, p / (p + q))
    GT -> (r, 0)

scaleDisc :: (Ord r, Num r) => r -> Disc r -> Disc r
scaleDisc s = foldMapDisc (\r p -> singleton r (s * p))
