{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Data.DeltaQ.Core
    ( DeltaQ (..)
    , exact
    , convolve
    , after
    , Ftf (..)
    , ftf
    ) where

import Data.DeltaQ.Probability

infixl 6 >>>

class (Ord p, Fractional p, Ord t, Monoid t, Monoid dq) => DeltaQ p t dq | dq -> p t where
    never    :: dq
    uniform  :: t -> t -> dq
    mix      :: Prob p -> dq -> dq -> dq
    smear    :: dq -> (Maybe t -> Maybe dq) -> Maybe dq
    (>>>)    :: dq -> Maybe t -> dq
    (<<<)    :: Maybe t -> dq -> Maybe dq
    before   :: dq -> Maybe t -> Maybe dq
    ftf'     :: dq -> dq -> Prob p
    sampleDQ :: MonadProb p m => dq -> m (Maybe t)

exact :: DeltaQ p t dq => t -> dq
exact t = uniform t t

convolve :: DeltaQ p t dq => dq -> dq -> dq
convolve x y = let Just z = smear x (Just . (y >>>)) in z

after :: DeltaQ p t dq => dq -> Maybe t -> Maybe dq
after x t = (>>> t) <$> t <<< x

data Ftf p t dq =
      First           dq (Maybe t -> Maybe dq)
    | Second                                   dq (Maybe t -> Maybe dq)
    | Mix    (Prob p) dq (Maybe t -> Maybe dq) dq (Maybe t -> Maybe dq)

ftf :: forall p t dq. DeltaQ p t dq => dq -> dq -> Ftf p t dq
ftf x y = case ftf' x y of
    p
        | p == 0    -> Second y (<<< x)
        | p == 1    -> First  x (<<< y)
        | otherwise ->
            let (x', i) = f x y
                (y', j) = f y x
            in  Mix p x' i y' j
  where
    f :: dq -> dq -> (dq, Maybe t -> Maybe dq)
    f a b = let Just c = smear b (before a) in (c, (<<< b))
