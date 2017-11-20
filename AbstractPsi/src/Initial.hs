{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Initial
    ( IPsi (..)
    , toInitial
    ) where

import Psi

data IPsi :: (* -> *) -> (* -> *) -> * where
    Done   :: IPsi c v
    Nu     :: (c a -> IPsi c v) -> IPsi c v
    Inp    :: c a -> (v a -> IPsi c v) -> IPsi c v
    Out    :: c a -> v a -> IPsi c v -> IPsi c v
    Fork   :: IPsi c v -> IPsi c v -> IPsi c v

instance Psi (IPsi c v) where
    type Chan (IPsi c v)  = c
    type Value (IPsi c v) = v
    done   = Done
    nu     = Nu
    inp    = Inp
    out    = Out
    fork   = Fork

toInitial :: (forall p. Psi p => p) -> IPsi c v 
toInitial = id
