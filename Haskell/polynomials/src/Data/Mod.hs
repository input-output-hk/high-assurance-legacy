{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Mod
    ( Mod (..)
    , (-+-)
    , (-~-)
    , FMod
    , EFMod (..)
    , fromFMod
    , toFMod
    ) where

import           Data.CMonoid
import           Data.Free
import           Data.Function (on)
import           Data.List     (foldl')
import           Data.Map      (Map)
import qualified Data.Map      as M
import           Data.Monoid   (Sum (..))

infixr 7 -*-
infixl 6 -+-
infixl 6 -~-

class (Num r, CMonoid m) => Mod r m | m -> r where
    (-*-) :: r -> m -> m
    neg :: m -> m

(-+-) :: Mod r m => m -> m -> m
(-+-) = (<>)

instance Num r => Mod r (Sum r) where
    s -*- Sum r = Sum $ s * r
    neg = negate

instance (Mod r m, Mod r n) => Mod r (m, n) where
    r -*- (x, y) = (r -*- x, r -*- y)
    neg (x, y) = (neg x, neg y)

instance Mod r m => Mod r (a -> m) where
    r -*- f = \x -> r -*- f x
    neg f = neg . f

(-~-) :: Mod r m => m -> m -> m
x -~- y = x -+- neg y

type FMod r = Free (Mod r) Set

instance Semigroup (FMod r a) where
    x <> y = Free $ \f -> free f x -+- free f y

instance Monoid (FMod r a) where
    mempty = Free $ const mempty

instance CMonoid (FMod r a) where

instance Num r => Mod r (FMod r a) where
    r -*- x = Free $ \f -> r -*- free f x
    neg x = Free $ \f -> neg $ free f x

newtype EFMod r a = EFMod (Map a r)
    deriving (Show, Eq, Ord)

instance (Eq r, Num r, Ord a) => Semigroup (EFMod r a) where
    EFMod m <> EFMod n = EFMod $ foldl' f m $ M.toList n
      where
        f :: Map a r -> (a, r) -> Map a r
        f m' (a, r) = M.alter (g r) a m'

        g :: r -> Maybe r -> Maybe r
        g r Nothing = Just r
        g r (Just r')
            | r + r' == 0 = Nothing
            | otherwise   = Just $ r + r'

instance (Eq r, Num r, Ord a) => Monoid (EFMod r a) where
    mempty = EFMod M.empty

instance (Eq r, Num r, Ord a) => CMonoid (EFMod r a) where

instance (Eq r, Num r, Ord a) => Mod r (EFMod r a) where
    r -*- EFMod m = EFMod $ if r == 0 then mempty else (* r) <$> m
    neg (EFMod m) = EFMod $ negate <$> m

fromFMod :: (Eq r, Num r, Ord a) => FMod r a -> EFMod r a
fromFMod = free $ \a -> EFMod $ M.singleton a 1

toFMod :: Num r => EFMod r a -> FMod r a
toFMod (EFMod m) = foldMap (\(a, r) -> r -*- basis a) $ M.toList m

instance (Eq r, Num r, Ord a) => Eq (FMod r a) where
    (==) = (==) `on` fromFMod

instance (Ord r, Num r, Ord a) => Ord (FMod r a) where
    compare = compare `on` fromFMod

instance (Show r, Eq r, Num r, Show a, Ord a) => Show (FMod r a) where
    show = show . fromFMod

instance (CMonoid a, Num r) => Num (FMod r a) where
    (+) = (<>)
    (-) = (-~-)
    x * y = flip free x $ \a -> flip free y $ \a' -> basis (a <> a')
    fromInteger n = Free $ \f -> fromInteger n -*- f mempty
    abs _ = error "abs not implemented"
    signum _ = error "signum not implemented"

