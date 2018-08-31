{-# LANGUAGE ScopedTypeVariables #-}

module Data.DeltaQ.Queue
    ( QueueDQ (..)
    , dequeueDQ
    , enqueueDQ
    , waitUntil
    , sampleQueueT
    , sampleQueueIO
    , sampleQueue
    ) where

import Control.Monad
import Control.Monad.Random    hiding (uniform)
import Data.DeltaQ.Core
import Data.DeltaQ.Monad
import Data.DeltaQ.Probability

data QueueDQ m a = Empty | Waiting (m (a, QueueDQ m a))

dequeueDQ :: Monad m => QueueDQ m a -> m (Maybe (a, QueueDQ m a))
dequeueDQ Empty       = return Nothing
dequeueDQ (Waiting m) = Just <$> m

enqueueDQ :: forall p t dq m a .
             MonadDeltaQ p t dq m
          => dq
          -> a
          -> QueueDQ m a
          -> QueueDQ m a
enqueueDQ dq a = go (delay dq)
  where
    go :: m () -> QueueDQ m a -> QueueDQ m a
    go d Empty         = Waiting $ d >> return (a, Empty)
    go d (Waiting maq) = Waiting $ do
        e <- d `race` maq
        return $ case e of
            Left  (()     , maq') -> (a , Waiting maq')
            Right ((a', q), d'  ) -> (a', go d' q)

waitUntil :: MonadDeltaQ p t dq m => (a -> Bool) -> QueueDQ m a -> m ()
waitUntil _ Empty       = delay never
waitUntil p (Waiting m) = do
    (a, q) <- m
    unless (p a) $ waitUntil p q

sampleQueueT :: Monad m => QueueDQ (SamplingDQT p t dq m) a -> SamplingT p m [(a, t)]
sampleQueueT Empty         = return []
sampleQueueT (Waiting maq) = do
    m <- runSamplingDQT maq
    case m of
        Nothing          -> return []
        Just ((a, q), t) -> ((a, t) :) <$> sampleQueueT q

sampleQueueIO :: QueueDQ (SamplingDQT p t dq IO) a -> IO [(a, t)]
sampleQueueIO = runSamplingT . sampleQueueT

sampleQueue :: Int -> QueueDQ (SamplingDQT p t dq (Rand StdGen)) a -> [(a, t)]
sampleQueue seed = (`evalRand` mkStdGen seed) . runSamplingT . sampleQueueT
