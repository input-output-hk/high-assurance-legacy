{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.DeltaQ.Queue
    ( QueueDQ (..)
    , emptyQueueDQ
    , enqueueDQ
    , filterDQ
    , waitUntil
    , sampleQueueT
    , sampleQueueIO
    , sampleQueue
    , QueueTree (..)
    , toTree
    ) where

import           Control.Arrow           (second)
import           Control.Monad.Random    hiding (uniform)
import           Data.DeltaQ.Core
import           Data.DeltaQ.Monad
import           Data.DeltaQ.Probability
import           Data.Map.Strict         (Map)
import qualified Data.Map.Strict         as M

newtype QueueDQ m a = QueueDQ {dequeueDQ :: m (Maybe (a, QueueDQ m a))}
    deriving Functor

instance (Show p, Show dq, Ord dq, Show a, Ord a, DeltaQ p t dq)
         => Show (QueueDQ (DeltaQM p t dq) a) where
    show = show . toTree

emptyQueueDQ :: Monad m => QueueDQ m a
emptyQueueDQ = QueueDQ $ return Nothing

enqueueDQ :: forall p t dq m a .
             MonadDeltaQ p t dq m
          => dq
          -> a
          -> QueueDQ m a
          -> QueueDQ m a
enqueueDQ dq a = go (delay dq)
  where
    go :: m () -> QueueDQ m a -> QueueDQ m a
    go d q = QueueDQ $ do
        e <- d `race` dequeueDQ q
        case e of
            Left  (() , m') -> return $ Just (a, QueueDQ m')
            Right (maq, d') -> case maq of
                Just (a', q') -> return $ Just (a', go d' q')
                Nothing       -> d' >> return (Just (a, emptyQueueDQ))

filterDQ :: Monad m => (a -> Bool) -> QueueDQ m a -> QueueDQ m a
filterDQ p q = QueueDQ $ do
    m <- dequeueDQ q
    case m of
        Nothing         -> return Nothing
        Just (a, q')
            | p a       -> return $ Just (a, filterDQ p q')
            | otherwise -> dequeueDQ $ filterDQ p q'

waitUntil :: MonadDeltaQ p t dq m => (a -> Bool) -> QueueDQ m a -> m ()
waitUntil p q = do
    m <- dequeueDQ q
    case m of
        Nothing         -> delay never
        Just (a, q')
            | p a       -> return ()
            | otherwise -> waitUntil p q'

sampleQueueT :: (DeltaQ p t dq, Monad m)
             => QueueDQ (SamplingDQT p t dq m) a
             -> SamplingT p m [(a, t)]
sampleQueueT = go now
  where
    go t q = do
        m <- runSamplingDQT (dequeueDQ q) t
        case m of
            Nothing                 -> return []
            Just (Nothing, _)       -> return []
            Just (Just (a, q'), t') -> ((a, t') :) <$> go t' q'

sampleQueueIO :: DeltaQ p t dq
              => QueueDQ (SamplingDQT p t dq IO) a
              -> IO [(a, t)]
sampleQueueIO = runSamplingT . sampleQueueT

sampleQueue :: DeltaQ p t dq
            => Int
            -> QueueDQ (SamplingDQT p t dq (Rand StdGen)) a
            -> [(a, t)]
sampleQueue seed = (`evalRand` mkStdGen seed) . runSamplingT . sampleQueueT

newtype QueueTree p dq a = QT [(Prob p, dq, a, QueueTree p dq a)]
    deriving (Show, Eq, Ord)

toTree :: forall p t dq a.
          (DeltaQ p t dq, Ord dq, Ord a)
       => QueueDQ (DeltaQM p t dq) a
       -> QueueTree p dq a
toTree q =
    let keys = filter (/= Nothing) $ M.keys m
        xs   = do
            k@(Just (a, t)) <- keys
            let (p, dq) = m M.! k
            return (p, dq, a, t)
    in QT xs
  where
    m :: Map (Maybe (a, QueueTree p dq a)) (Prob p, dq)
    m = runDeltaQM $ f <$> dequeueDQ q

    f :: Maybe (a, QueueDQ (DeltaQM p t dq) a) -> Maybe (a, QueueTree p dq a)
    f = fmap $ second toTree
