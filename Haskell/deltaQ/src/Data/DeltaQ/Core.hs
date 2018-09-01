{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Data.DeltaQ.Core
    ( Time
    , now
    , Ext (..)
    , DeltaQ (..)
    , never
    , Ftf (..)
    , ftf
    ) where

import Data.DeltaQ.Probability

class (Ord a, Monoid a) => Time a where

now :: Time a => a
now = mempty

data Ext a = Finite !a | Infinity
    deriving (Eq, Ord)

instance Show a => Show (Ext a) where
    show (Finite a) = show a
    show Infinity   = "∞"

instance Semigroup a => Semigroup (Ext a) where
    Infinity <> _        = Infinity
    _        <> Infinity = Infinity
    Finite m <> Finite n = Finite $ m <> n

instance Monoid a => Monoid (Ext a) where
    mempty = Finite mempty

instance Time a => Time (Ext a) where

class (Ord p, Fractional p, Time t, Monoid dq) => DeltaQ p t dq | dq -> p t where
    massive  :: dq -> Maybe (Prob p, dq)
    exact    :: Ext t -> dq
    mix      :: Prob p -> dq -> dq -> dq
    before   :: dq -> dq -> Maybe (Prob p, dq)
    after    :: dq -> dq -> Maybe (Prob p, dq)
    maxDQ    :: dq -> dq -> dq
    sampleDQ :: MonadProb p m => dq -> m (Maybe t)

never :: DeltaQ p t dq => dq
never = exact Infinity

data Ftf p t dq =
      Never
    | First  (Prob p) dq
    | Second             (Prob p) dq
    | Mix    (Prob p) dq (Prob p) dq
    deriving (Show, Eq, Ord)

ftf :: DeltaQ p t dq => dq -> dq -> Ftf p t dq
ftf x y = case (x `before` y, y `before` x) of
    (Just (px, dqx), Nothing       ) -> First  px dqx
    (Nothing       , Just (py, dqy)) -> Second py dqy
    (Nothing       , Nothing       ) -> Never
    (Just (px, dqx), Just (py, dqy)) -> Mix px dqx py dqy
