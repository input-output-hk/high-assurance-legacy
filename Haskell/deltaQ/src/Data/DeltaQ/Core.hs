{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Data.DeltaQ.Core
    ( Time (..)
    , now
    , Ext (..)
    , DeltaQ (..)
    , mass
    , never
    ) where

import Data.DeltaQ.Probability

class (Show a, Ord a, Monoid a) => Time a where
    fromTime :: a -> Double
    diff :: a -> a -> Maybe a

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

    fromTime (Finite t) = fromTime t
    fromTime Infinity   = 1 / 0

    diff (Finite t) (Finite s) = Finite <$> diff t s
    diff Infinity   _          = Just Infinity
    diff (Finite _) Infinity   = Nothing

class (Show p, Fractional p, Real p, Time t, Show dq, Ord dq, Monoid dq) =>
      DeltaQ p t dq | dq -> p t where
    massive  :: dq -> Maybe (Prob p, dq)
    exact    :: Ext t -> dq
    mix      :: Prob p -> dq -> dq -> dq
    before   :: dq -> [dq] -> Maybe (Prob p, dq, [dq])
    sampleDQ :: MonadProb p m => dq -> m (Maybe t)

never :: DeltaQ p t dq => dq
never = exact Infinity

mass :: DeltaQ p t dq => dq -> Prob p
mass dq = case massive dq of
    Nothing     -> 0
    Just (p, _) -> p
