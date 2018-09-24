{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.DeltaQ.Queue
    ( Queue (..)
    , emptyQueue
    , dequeue
    , enqueue
    ) where

import Data.DeltaQ.Core
import Data.DeltaQ.Probability

newtype Queue p t dq m a = Queue ([(a, dq, dq)] -> m (Maybe (a, dq, dq, Queue p t dq m a)))

instance Show (Queue p t dq m a) where
    show = const "Queue"

enqueue' :: a -> dq -> dq -> Queue p t dq m a -> Queue p t dq m a
enqueue' a dqRel dqAbs (Queue f) = Queue $ \xs -> f ((a, dqRel, dqAbs) : xs)

dequeue :: Queue p t dq m a -> m (Maybe (a, dq, dq, Queue p t dq m a))
dequeue (Queue f) = f []

emptyQueue :: (DeltaQ p t dq, MonadProb p m) => Queue p t dq m a
emptyQueue = Queue $ foldr f (return Nothing)
  where
    f (a, dqaRel, dqaAbs) x = do
        m <- x
        case m of
            Nothing -> return $ Just (a, dqaRel, dqaAbs, emptyQueue)
            Just (b, dqbRel, dqbAbs, q) ->
                case before dqaRel dqbRel of
                    Nothing -> do
                        let Just (_, _, dqaRel') = before dqbRel dqaRel
                            Just dqaAbs'         = after dqaAbs dqbAbs
                        return $ Just (b, dqbRel, dqbAbs, enqueue' a dqaRel' dqaAbs' q)
                    Just (1, _, dqbRel') ->
                        return $ Just (a, dqaRel, dqaAbs, enqueue' b dqbRel' dqbAbs q)
                    Just (p, dqaRel1, dqbRel1) -> do
                        let Just (_, dqaAbs1, _)       = before dqaAbs dqbAbs
                            Just dqbAbs1               = after dqbAbs dqaAbs
                            Just (_, dqbRel2, dqaRel2) = before dqbRel dqaRel
                            Just (_, dqbAbs2, _)       = before dqbAbs dqaAbs
                            Just dqaAbs2               = after dqaAbs dqbAbs
                        coin p
                            (Just (a, dqaRel1, dqaAbs1, enqueue' b dqbRel1 dqbAbs1 q))
                            (Just (b, dqbRel2, dqbAbs2, enqueue' a dqaRel2 dqaAbs2 q))

enqueue :: (DeltaQ p t dq, MonadProb p m)
        => a
        -> dq
        -> dq
        -> Queue p t dq m a
        -> Queue p t dq m a
enqueue a dqRel dqAbs (Queue f) = Queue $ \xs -> case massive dqRel of
    Nothing          -> f xs
    Just (p, dqRel') ->
        let Just (_, dqAbs') = massive dqAbs
        in  coinM p (f $ (a, dqRel', dqAbs') : xs) (f xs)
