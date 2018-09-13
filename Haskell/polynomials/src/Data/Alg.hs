{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Data.Alg
    ( Alg (..)
    , Algebra (..)
    , ComposedAlgebras (..)
    , FAlg
    , fromFAlg
    , toFAlg
    ) where

import Data.CMonoid
import Data.Free
import Data.Function (on)
import Data.Mod

class (Num r, Num s) => Alg r s | s -> r where
    iota :: r -> s

newtype Algebra a = Algebra {getAlgebra :: a}
    deriving (Show, Read, Eq, Ord, Num)

instance Num a => Alg a (Algebra a) where
    iota = Algebra

newtype ComposedAlgebras r s t = ComposedAlgebras {getComposedAlgebras :: t}
    deriving (Show, Read, Eq, Ord, Num)

instance (Alg r s, Alg s t) => Alg r (ComposedAlgebras r s t) where
    iota = ComposedAlgebras . iota . iota

type FAlg r = Free (Alg r) CMonoid

instance CMonoid a => Num (FAlg r a) where
    x + y = Free $ \f -> free f x + free f y
    x * y = Free $ \f -> free f x * free f y
    x - y = Free $ \f -> free f x - free f y
    fromInteger n = Free $ const $ fromInteger n
    abs x = Free $ \f -> abs $ free f x
    signum x = Free $ \f -> signum $ free f x

instance (Num r, CMonoid a) => Alg r (FAlg r a) where
    iota r = Free $ const $ iota r

instance (CMonoid a, Num r) => Semigroup (FAlg r a) where
    (<>) = (+)

instance (CMonoid a, Num r) => Monoid (FAlg r a) where
    mempty = 0

instance (CMonoid a, Num r) => CMonoid (FAlg r a) where

instance (CMonoid a, Num r) => Mod r (FAlg r a) where
    r -*- x = iota r * x
    neg = negate

instance (CMonoid a, Num r) => Alg r (FMod r a) where
    iota r = Free $ \f -> r -*- f mempty

fromFAlg :: (CMonoid a, Num r) => FAlg r a -> FMod r a
fromFAlg = free basis

toFAlg :: (CMonoid a, Num r) => FMod r a -> FAlg r a
toFAlg = free basis

instance (CMonoid a, Ord a, Num r, Eq r) => Eq (FAlg r a) where
    (==) = (==) `on` fromFAlg

instance (CMonoid a, Ord a, Num r, Ord r) => Ord (FAlg r a) where
    compare = compare `on` fromFAlg

instance (CMonoid a, Show a, Ord a, Num r, Show r, Eq r) => Show (FAlg r a) where
    show = show . fromFAlg
