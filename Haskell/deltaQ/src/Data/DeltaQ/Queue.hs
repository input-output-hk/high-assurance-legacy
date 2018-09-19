{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.DeltaQ.Queue
    ( Queue (..)
    , emptyQueue
    , enqueue
    , filterQueue
    ) where

import Data.DeltaQ.Core
import Data.DeltaQ.Probability

newtype Queue p t dq m a = Queue {dequeue :: m (Maybe (dq, a, Queue p t dq m a))}
    deriving Functor

instance Show (Queue p t dq m a) where
    show = const "Queue"

emptyQueue :: Monad m => Queue p t dq m a
emptyQueue = Queue $ return Nothing

enqueue :: (DeltaQ p t dq, MonadProb p m)
        => dq
        -> a
        -> Queue p t dq m a
        -> Queue p t dq m a
enqueue dqa a q = case massive dqa of
    Nothing        -> q
    Just (p, dqa') -> Queue $ do
        m <- dequeue q
        coinM (1 - p) (return m) $ Just <$> case m of
            Nothing           -> return (dqa', a, emptyQueue)
            Just (dqb, b, q') -> case before dqa' dqb of
                Nothing               -> do
                    let Just (_, _, dqa'') = before dqb dqa'
                        q''                = enqueue dqa'' a q'
                    return (dqb, b, q'')
                Just (pa, dqa'', dqb') -> coin pa
                    (dqa'', a, Queue $ return $ Just (dqb', b, q'))
                    (let Just (_, dqb'', dqa''') = before dqb dqa'
                     in  (dqb'', b, enqueue dqa''' a q'))

filterQueue :: (DeltaQ p t dq, Monad m)
            => (a -> Bool)
            -> Queue p t dq m a
            -> Queue p t dq m a
filterQueue p = go mempty
  where
    go dq q = Queue $ do
        m <- dequeue q
        case m of
            Nothing           -> return Nothing
            Just (dq', a, q')
                | p a         -> return $ Just (dq <> dq', a, go mempty q')
                | otherwise   -> dequeue $ go (dq <> dq') q'
