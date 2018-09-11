{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.DeltaQ.Queue
    ( Queue (..)
    , emptyQueue
    , enqueue
    , dequeue
    , filterQueue
    ) where

import Control.Arrow           (first)
import Data.DeltaQ.Core
import Data.DeltaQ.Probability
import Data.Maybe              (mapMaybe)

data Queue p t dq a = Queue {getQueue :: [(dq, a)]}
    deriving (Show, Eq, Ord, Functor)

emptyQueue :: Queue p t dq a
emptyQueue = Queue []

enqueue :: (DeltaQ p t dq, MonadProb p m)
        => dq
        -> a
        -> Queue p t dq a
        -> m (Queue p t dq a)
enqueue dq a q@(Queue xs) = case massive dq of
    Nothing       -> return q
    Just (p, dq') -> coin p (Queue $ (dq', a) : xs) q

dequeue :: forall p t dq m a .
           (DeltaQ p t dq, MonadProb p m)
        => Queue p t dq a
        -> Maybe (m (dq, a, Queue p t dq a))
dequeue (Queue [])        = Nothing
dequeue (Queue [(dq, a)]) = Just $ return (dq, a, emptyQueue)
dequeue (Queue xs)        = Just $ do
    let ys = mapMaybe (uncurry f) $ picks xs
    weighted ys
  where
    f :: (dq, a) -> [(dq, a)] -> Maybe (Prob p, (dq, a, Queue p t dq a))
    f (dq, a) dqas = case dq `before` map fst dqas of
        Nothing             -> Nothing
        Just (p, dq', dqs') ->
            let dqas' = zipWith (\dq'' (_, b) -> (dq'', b)) dqs' dqas
            in  Just (p, (dq', a, Queue dqas'))

picks :: [a] -> [(a, [a])]
picks []       = []
picks (x : xs) = (x, xs) : [(y, x : ys) | (y, ys) <- picks xs]

weighted :: MonadProb p m => [(Prob p, a)] -> m a
weighted []            = error "impossible case"
weighted [(_, a)]      = return a
weighted ((0, _) : xs) = weighted xs
weighted ((1, a) : _)  = return a
weighted ((p, a) : xs) =
    coinM p
        (return a)
        (weighted $ map (first (/ (1 - p))) xs)

filterQueue :: (a -> Bool) -> Queue p t dq a -> Queue p t dq a
filterQueue p = Queue . filter (p . snd) . getQueue
