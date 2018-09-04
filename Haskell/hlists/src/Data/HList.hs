{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.HList
    ( All
    , K (..)
    , I (..)
    , NP (..)
    , NS (..)
    , hmap
    , Index (..)
    , fromIndex
    , pair
    , (!)
    , set
    , IsNP (..)
    , replicateNP
    ) where

import Data.Functor.Identity (Identity (..))
import Data.Kind

type family All (f :: k -> Type) (xs :: [k]) (c :: Type -> Constraint) :: Constraint where
    All f '[]       c = ()
    All f (x ': xs) c = (c (f x), All f xs c)

infixr 5 :*

data NP (f :: k -> Type) (xs :: [k]) :: Type where
    Nil  :: NP f '[]
    (:*) :: f x -> NP f xs -> NP f (x ': xs)

hmap :: (forall a. f a -> g a) -> NP f xs -> NP g xs
hmap _  Nil       = Nil
hmap mu (x :* xs) = mu x :* hmap mu xs

deriving instance All f xs Show => Show (NP f xs)
deriving instance All f xs Eq => Eq (NP f xs)
deriving instance (All f xs Eq, All f xs Ord) => Ord (NP f xs)

newtype K a b = K {unK :: a}
    deriving (Show, Eq, Ord, Functor)

newtype I a = I {unI :: a}
    deriving (Show, Eq, Ord, Functor)

data NS (f :: k -> Type) (xs :: [k]) :: Type where
    Z :: f x -> NS f (x ': xs)
    S :: NS f xs -> NS f (x ': xs)

deriving instance All f xs Show => Show (NS f xs)
deriving instance All f xs Eq => Eq (NS f xs)
deriving instance (All f xs Eq, All f xs Ord) => Ord (NS f xs)

data Index (x :: k) (xs :: [k]) :: Type where
    Here  :: Index x (x ': xs)
    There :: Index x xs -> Index x (y ': xs)

fromIndex :: Index x xs -> f x -> NS f xs
fromIndex Here      = Z
fromIndex (There i) = S . fromIndex i

pair :: Monad m
     => (forall a. f a -> g a -> m (g a, b))
     -> NS f xs
     -> NP g xs
     -> m (NP g xs, b)
pair mu (Z x) xs = case xs of
    (y :* ys) -> mu x y       >>= \(y', b)  -> return (y' :* ys, b)
pair mu (S u) xs = case xs of
    (y :* ys) -> pair mu u ys >>= \(ys', b) -> return (y :* ys', b)

(!) :: NP f xs -> Index x xs -> f x
(!) xs Here      = case xs of (a :* _ ) -> a
(!) xs (There i) = case xs of (_ :* ys) -> ys ! i

set :: forall f x xs. Index x xs -> f x -> NP f xs -> NP f xs
set i x = fst . runIdentity . pair mu (fromIndex i x)
  where
    mu :: f a -> f a -> Identity (f a, ())
    mu x' _ = return (x', ())

class IsNP (xs :: [k]) where
    induct :: f '[] -> (forall y ys. f ys -> f (y ': ys)) -> f xs

instance IsNP '[] where
    induct nil _ = nil

instance IsNP xs => IsNP (x ': xs) where
    induct nil cons = cons $ induct nil cons

replicateNP :: IsNP xs => (forall x. f x) -> NP f xs
replicateNP x = induct Nil $ \ys -> x :* ys
