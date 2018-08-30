{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.List.FixedLength (

    List (Empty, (:::)),
    map,
    zipWith,
    iterate,
    firstNaturals

) where

import Prelude hiding (map, zipWith, iterate, repeat)

import Control.Applicative (liftA2)

import Data.Foldable (toList)
import Data.Type.Natural (Natural (Z, S), TypeNatural (induct))

infixr 5 :::

data List n a where

    Empty :: List 'Z a

    (:::) :: a -> List n a -> List ('S n) a

deriving instance Eq a => Eq (List n a)

deriving instance Ord a => Ord (List n a)

deriving instance Show a => Show (List n a)

instance Functor (List n) where

    fmap = map

    _ <$ Empty    = Empty
    x <$ _ ::: ys = x ::: (x <$ ys)

instance TypeNatural n => Applicative (List n) where

    pure = repeat

    liftA2 = zipWith

    (*>) = flip const

    (<*) = const

instance TypeNatural n => Monad (List n) where

    xs >>= f = zipWith (!!) (map (toList . f) xs) firstNaturals

    (>>) = (*>)

instance Foldable (List n) where

    foldMap _ Empty      = mempty
    foldMap f (x ::: xs) = f x <> foldMap f xs

    -- FIXME: Perhaps implement other methods explicitly.

instance Traversable (List n) where

    traverse _ Empty      = pure Empty
    traverse f (x ::: xs) = liftA2 (:::) (f x) (traverse f xs)

    -- FIXME: Perhaps implement other methods explicitly.

map :: (a -> b) -> List n a -> List n b
map _ Empty      = Empty
map f (x ::: xs) = f x ::: map f xs

zipWith :: (a -> b -> c) -> List n a -> List n b -> List n c
zipWith _ Empty      Empty      = Empty
zipWith f (x ::: xs) (y ::: ys) = f x y ::: zipWith f xs ys

newtype Iterate a n = Iterate {
    plainIterate :: a -> List n a
}

iterate :: TypeNatural n => (a -> a) -> a -> List n a
iterate f = plainIterate $
            induct (Iterate $ const Empty)
                   (\ h -> Iterate $ \ x -> x ::: plainIterate h (f x))

repeat :: TypeNatural n => a -> List n a
repeat = iterate id

firstNaturals :: (TypeNatural n, Enum a, Num a) => List n a
firstNaturals = iterate succ 0
