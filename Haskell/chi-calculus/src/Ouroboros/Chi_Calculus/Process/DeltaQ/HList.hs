{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Ouroboros.Chi_Calculus.Process.DeltaQ.HList (

    HList (..),
    HIndex (..),
    (!),
    hmap,
    hzipWith,
    toList,
    All

) where

import Data.Functor.Const (Const (..))
import GHC.Exts           (Constraint)

infixr 5 :::

data HList (f :: * -> *) (ts :: [*]) where
    Nil   :: HList f '[]
    (:::) :: f t -> HList f ts -> HList f (t ': ts)

data HIndex t (ts :: [*]) where
    Here  :: HIndex t (t ': ts)
    There :: HIndex t' ts -> HIndex t' (t ': ts)

(!) :: HList f ts -> HIndex t ts -> f t
(!) = flip f
  where
    f :: HIndex t ts -> HList f ts -> f t
    f Here      (x ::: _)  = x
    f (There i) (_ ::: xs) = f i xs

hmap :: (forall a. f a -> g a) -> HList f ts -> HList g ts
hmap _ Nil        = Nil
hmap f (x ::: xs) = f x ::: hmap f xs

hzipWith :: (forall a. f a -> g a -> h a) -> HList f ts -> HList g ts -> HList h ts
hzipWith _ Nil        Nil        = Nil
hzipWith f (x ::: xs) (y ::: ys) = f x y ::: hzipWith f xs ys

toList :: HList (Const a) ts -> [a]
toList Nil              = []
toList (Const a ::: xs) = a : toList xs

type family All (c :: * -> Constraint) (f :: * -> *) (ts :: [*]) :: Constraint where
    All c f '[]       = ()
    All c f (t ': ts) = (c (f t), All c f ts)

deriving instance (All Show f ts) => Show (HList f ts)
deriving instance (All Eq f ts) => Eq (HList f ts)
