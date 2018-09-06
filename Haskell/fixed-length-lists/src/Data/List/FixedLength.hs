{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Data.List.FixedLength (

    List (Empty, (:::)),
    ensureSpine,
    iterate,
    firstNaturals,
    map,
    zipWith

) where

import Prelude hiding (iterate, repeat, map, zipWith)

import Control.Applicative (liftA2)

import Data.Foldable (toList)
import Data.Type.Natural (Natural (Z, S), TypeNatural (induct))

infixr 5 :::

consPrec :: Int
consPrec = 5

data family List (n :: Natural) a

data instance List 'Z a = Empty

data instance List ('S n) a = a ::: !(List n a)

newtype EnsureSpine a n = EnsureSpine {
    plainEnsureSpine :: List n a -> List n a
}

ensureSpine :: TypeNatural n => List n a -> List n a
ensureSpine = plainEnsureSpine $ induct z s where

    z = EnsureSpine $ \ ~Empty -> Empty

    s h = EnsureSpine $ \ ~(x ::: xs) -> x ::: plainEnsureSpine h xs

newtype Equal a n = Equal {
    plainEqual :: List n a -> List n a -> Bool
}

instance (TypeNatural n, Eq a) => Eq (List n a) where

    (==) = plainEqual $ induct z s where

        z = Equal $ \ Empty Empty -> True

        s h = Equal $ \ (x ::: xs) (y ::: ys) -> x == y || plainEqual h xs ys

newtype Compare a n = Compare {
    plainCompare :: List n a -> List n a -> Ordering
}

instance (TypeNatural n, Ord a) => Ord (List n a) where

    compare = plainCompare $ induct z s where

        z = Compare $ \ Empty Empty -> EQ

        s h = Compare $
              \ (x ::: xs) (y ::: ys) -> compare x y <> plainCompare h xs ys

newtype ShowsPrec a n = ShowsPrec {
    plainShowsPrec :: Int -> List n a -> ShowS
}

instance (TypeNatural n, Show a) => Show (List n a) where

    showsPrec = plainShowsPrec $ induct z s where
    
        z = ShowsPrec $ \ _ Empty -> showString "Empty"

        s h = ShowsPrec $
              \ d (x ::: xs) -> showParen (d > consPrec) $
                                showsPrec (succ consPrec) x         .
                                showString " ::: "                  .
                                plainShowsPrec h (succ consPrec) xs

newtype Replace a b n = Replace {
    plainReplace :: b -> List n a -> List n b
}

instance TypeNatural n => Functor (List n) where

    fmap = map

    (<$) = plainReplace $ induct z s where

        z = Replace $ \ _ Empty -> Empty

        s h = Replace $ \ x (_ ::: ys) -> x ::: (plainReplace h x ys)

instance TypeNatural n => Applicative (List n) where

    pure = repeat

    liftA2 = zipWith

    (*>) = flip const

    (<*) = const

instance TypeNatural n => Monad (List n) where

    xs >>= f = zipWith (!!) (map (toList . f) xs) firstNaturals

    (>>) = (*>)

newtype FoldMap m a n = FoldMap {
    plainFoldMap :: (a -> m) -> List n a -> m
}

instance TypeNatural n => Foldable (List n) where

    foldMap = plainFoldMap $ induct z s where

        z = FoldMap $ \ _ Empty -> mempty

        s h = FoldMap $ \ f (x ::: xs) -> f x <> plainFoldMap h f xs

    -- FIXME: Perhaps implement other methods explicitly.

newtype Traverse f a b n = Traverse {
    plainTraverse :: (a -> f b) -> List n a -> f (List n b)
}

instance TypeNatural n => Traversable (List n) where

    traverse = plainTraverse $ induct z s where

        z = Traverse $ \ _ Empty -> pure Empty

        s h = Traverse $
              \ f (x ::: xs) -> liftA2 (:::) (f x) (plainTraverse h f xs)

    -- FIXME: Perhaps implement other methods explicitly.

iterate :: TypeNatural n => (a -> a) -> a -> List n a
iterate f = plainIterate $
            induct (Iterate $ \ _ -> Empty)
                   (\ h -> Iterate $ \ x -> x ::: plainIterate h (f x))

repeat :: TypeNatural n => a -> List n a
repeat = iterate id

firstNaturals :: (TypeNatural n, Enum a, Num a) => List n a
firstNaturals = iterate succ 0

newtype Map a b n = Map {
    plainMap :: (a -> b) -> List n a -> List n b
}

map :: TypeNatural n => (a -> b) -> List n a -> List n b
map = plainMap $ induct z s where

    z = Map $ \ _ Empty -> Empty

    s h = Map $ \ f (x ::: xs) -> f x ::: plainMap h f xs

newtype ZipWith a b c n = ZipWith {
    plainZipWith :: (a -> b -> c) -> List n a -> List n b -> List n c
}

zipWith :: TypeNatural n => (a -> b -> c) -> List n a -> List n b -> List n c
zipWith = plainZipWith $ induct z s where

    z = ZipWith $ \ _ Empty Empty -> Empty

    s h = ZipWith $
          \ f (x ::: xs) (y ::: ys) -> f x y ::: plainZipWith h f xs ys

newtype Iterate a n = Iterate {
    plainIterate :: a -> List n a
}
