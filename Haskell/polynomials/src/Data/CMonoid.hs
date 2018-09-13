{-# LANGUAGE FlexibleInstances #-}

module Data.CMonoid
    ( CMonoid
    , FCMonoid
    , EFCMonoid (..)
    , fromFCMonoid
    , toFCMonoid
    , (^^^)
    ) where

import           Data.Free
import           Data.Function   (on)
import           Data.Map        (Map)
import qualified Data.Map        as M
import           Data.Monoid     (Product (..), Sum (..))
import           Numeric.Natural

class Monoid a => CMonoid a where

instance Num a => CMonoid (Sum a) where
instance Num a => CMonoid (Product a) where
instance (CMonoid a, CMonoid b) => CMonoid (a, b) where
instance CMonoid a => CMonoid (b -> a) where

type FCMonoid = Free CMonoid Set

instance Semigroup (FCMonoid a) where
    x <> y = Free $ \f -> free f x <> free f y

instance Monoid (FCMonoid a) where
    mempty = Free $ const mempty

instance CMonoid (FCMonoid a) where

newtype EFCMonoid a = EFCMonoid (Map a (Sum Natural))
    deriving (Show, Eq, Ord)

instance Ord a => Semigroup (EFCMonoid a) where
    EFCMonoid m <> EFCMonoid n = EFCMonoid $ M.unionWith (<>) m n

instance Ord a => Monoid (EFCMonoid a) where
    mempty = EFCMonoid M.empty

instance Ord a => CMonoid (EFCMonoid a) where


infixl 8 ^^^

(^^^) :: Monoid a => a -> Natural -> a
_ ^^^ 0      = mempty
a ^^^ n      =
    let n' = n `div` 2
        b  = a ^^^ n'
        b' = b <> b
    in  if even n then b' else b' <> a

fromFCMonoid :: Ord a => FCMonoid a -> EFCMonoid a
fromFCMonoid = free $ \a -> EFCMonoid $ M.singleton a (Sum 1)

toFCMonoid :: EFCMonoid a -> FCMonoid a
toFCMonoid (EFCMonoid m) = foldMap (\(a, Sum n) -> basis a ^^^ n) $ M.toList m

instance Ord a => Eq (FCMonoid a) where
    (==) = (==) `on` fromFCMonoid

instance Ord a => Ord (FCMonoid a) where
    compare = compare `on` fromFCMonoid

instance (Show a, Ord a) => Show (FCMonoid a) where
    show = show . fromFCMonoid
