{-# LANGUAGE ScopedTypeVariables #-}

module Data.DeltaQ.Queue
    ( Queue (..)
    , emptyQueue
    , dequeue
    , enqueue
    ) where

import Data.DeltaQ.Core
import Data.DeltaQ.Probability

newtype Queue p t dq m a = Queue ([(a, dq)] -> m (Maybe (a, dq, Queue p t dq m a)))

instance Show (Queue p t dq m a) where
    show = const "Queue"

dequeue :: Queue p t dq m a -> m (Maybe (a, dq, Queue p t dq m a))
dequeue (Queue f) = f []

joinQueue :: Monad m => m (Queue p t dq m a) -> Queue p t dq m a
joinQueue m = Queue $ \xs -> do
    Queue f <- m
    f xs

enqueue' :: a -> dq -> Queue p t dq m a -> Queue p t dq m a
enqueue' a dq (Queue f) = Queue $ \xs -> f ((a, dq) : xs)

enqueue :: (DeltaQ p t dq, MonadProb p m)
        => a
        -> dq
        -> Queue p t dq m a
        -> Queue p t dq m a
enqueue a dq q = case massive dq of
    Nothing       -> q
    Just (p, dq') -> joinQueue $ coin p (enqueue' a dq' q) q

emptyQueue :: forall p t dq m a. (DeltaQ p t dq, MonadProb p m) => Queue p t dq m a
emptyQueue = Queue $ foldr f $ return Nothing
  where
    f :: (a, dq)
      -> m (Maybe (a, dq, Queue p t dq m a))
      -> m (Maybe (a, dq, Queue p t dq m a))
    f (a, dqa) x = do
        m <- x
        case m of
            Nothing          -> return $ Just (a, dqa, emptyQueue)
            Just (b, dqb, q) ->
                case before dqa dqb of
                    Nothing -> do
                        let Just (_, _, dqa') = before dqb dqa
                        return $ Just (b, dqb, enqueue' a dqa' q)
                    Just (1, _, dqb') ->
                        return $ Just (a, dqa, enqueue' b dqb' q)
                    Just (p, dqa1, dqb1) -> do
                        let Just (_, dqb2, dqa2) = before dqb dqa
                        Just <$> coin p
                            (a, dqa1, enqueue' b dqb1 q)
                            (b, dqb2, enqueue' a dqa2 q)
