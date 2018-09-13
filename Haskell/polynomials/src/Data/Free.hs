{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE RankNTypes        #-}

module Data.Free
    ( Free (..)
    , free
    , basis
    , Set
    ) where

import Data.Kind

data Free (c :: Type -> Constraint)
          (d :: Type -> Constraint)
          (a :: Type)
          :: Type where
    Free :: d a => (forall x. c x => (a -> x) -> x) -> Free c d a

free :: c x => (a -> x) -> Free c d a -> x
free f (Free x) = x f

basis :: d a => a -> Free c d a
basis a = Free $ \f -> f a

class Set a where

instance Set a where
