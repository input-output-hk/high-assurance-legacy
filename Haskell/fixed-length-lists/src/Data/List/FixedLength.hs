module Data.List.FixedLength (

    List (Empty, (:::)),
    map,
    zipWith,
    iterate,
    firstNaturals

) where

import Prelude hiding (map, zipWith, iterate, repeat)

import Data.Type.Natural (Natural (Z, S), TypeNatural (induct))

infixr 5 :::

data List n a where

    Empty :: List 'Z a

    (:::) :: a -> List n a -> List ('S n) a

deriving instance Eq a => Eq (List n a)

deriving instance Ord a => Ord (List n a)

deriving instance Show a => Show (List n a)

map :: (a -> b) -> List n a -> List n b
map _ Empty      = Empty
map f (x ::: xs) = f x ::: map f xs

zipWith :: (a -> b -> c) -> List n a -> List n b -> List n c
zipWith _ Empty      Empty      = Empty
zipWith f (x ::: xs) (y ::: ys) = f x y ::: zipWith f xs ys

newtype IterateAccum a n = IterateAccum { fromIterateAccum :: a -> List n a }

iterate :: TypeNatural n => (a -> a) -> a -> List n a
iterate f = fromIterateAccum $
            induct (IterateAccum $ const Empty)
                   (\ h -> IterateAccum $ \ x -> x ::: fromIterateAccum h (f x))

repeat :: TypeNatural n => a -> List n a
repeat = iterate id

firstNaturals :: (TypeNatural n, Enum a, Num a) => List n a
firstNaturals = iterate succ 0
