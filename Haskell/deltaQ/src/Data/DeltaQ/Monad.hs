{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Data.DeltaQ.Monad
    ( MonadDeltaQ (..)
    , SamplingDQT (..)
    , DeltaQT
    , DeltaQM
    , runDeltaQT
    , runDeltaQM
    , liftQT
    , timing
    ) where

import           Control.Monad
import           Control.Monad.Random    hiding (uniform)
import           Data.DeltaQ.Core
import           Data.DeltaQ.Probability
import           Data.List               (foldl')
import           Data.Map.Strict         (Map)
import qualified Data.Map.Strict         as M

class (DeltaQ p t dq, MonadProb p m) => MonadDeltaQ p t dq m | m -> p t dq where
    delay      :: dq -> m ()
    race       :: m a -> m b -> m (Either (a, m b) (b, m a))

newtype SamplingDQT p t dq m a =
    SamplingDQT {runSamplingDQT :: t -> SamplingT p m (Maybe (a, t))}

instance (DeltaQ p t dq, Monad m) => Functor (SamplingDQT p t dq m) where
    fmap = liftM

instance (DeltaQ p t dq, Monad m) => Applicative (SamplingDQT p t dq m) where
    pure = return
    (<*>) = ap

instance (DeltaQ p t dq, Monad m) => Monad (SamplingDQT p t dq m) where

    return x = SamplingDQT $ \t -> return $ Just (x, t)

    ma >>= cont = SamplingDQT $ \t -> do
        x <- runSamplingDQT ma t
        case x of
            Nothing     -> return Nothing
            Just (a, ta) -> do
                y <- runSamplingDQT (cont a) ta
                case y of
                    Nothing      -> return Nothing
                    Just (b, tb) -> return $ Just (b, tb)

instance (DeltaQ p t dq, Random p, MonadRandom m) =>
         MonadProb p (SamplingDQT p t dq m) where
    coin p x y = SamplingDQT $ \t -> coin p (Just (x, t)) (Just (y, t))

instance forall p t dq m. (DeltaQ p t dq, Random p, MonadRandom m) =>
         MonadDeltaQ p t dq (SamplingDQT p t dq m) where

    delay dq = SamplingDQT $ \t -> do
        ms <- sampleDQ dq
        case ms of
            Nothing -> return Nothing
            Just s  -> return $ Just ((), t <> s)

    race x y = SamplingDQT $ \t -> do
        mx <- runSamplingDQT x t
        my <- runSamplingDQT y t
        case (mx, my) of
            (Nothing, Nothing)           ->
                    return Nothing
            (Just (a, ta), Nothing)      ->
                    return $ Just (Left  (a, SamplingDQT $ const $ return Nothing), ta)
            (Nothing, Just (b, tb))      ->
                    return $ Just (Right (b, SamplingDQT $ const $ return Nothing), tb)
            (Just (a, ta), Just (b, tb)) -> do
                let ma = Just (Left  (a, SamplingDQT $ \t' -> return $ Just (b, max t' tb)) , ta)
                    mb = Just (Right (b, SamplingDQT $ \t' -> return $ Just (a, max t' ta)) , tb)
                case compare ta tb of
                    LT -> return ma
                    GT -> return mb
                    EQ -> coin 0.5 ma mb

newtype DeltaQT p t dq m a = DeltaQT {runDeltaQT' :: dq -> m (Maybe (a, dq))}

runDeltaQT :: DeltaQ p t dq => DeltaQT p t dq m a -> m (Maybe (a, dq))
runDeltaQT m = runDeltaQT' m mempty

type DeltaQM p t dq = DeltaQT p t dq (ProbM p)

runDeltaQM :: forall a p t dq. (Ord a, DeltaQ p t dq, Ord dq)
           => DeltaQM p t dq a
           -> Map a (Prob p, dq)
runDeltaQM x = foldl' f M.empty $ M.toList m
  where
    m :: Map (Maybe (a, dq)) (Prob p)
    m = runProbM $ runDeltaQT x

    f :: Map a (Prob p, dq)
      -> (Maybe (a, dq), Prob p)
      -> Map a (Prob p, dq)
    f n (Nothing     , _) = n
    f n (Just (a, dq), p) = M.insertWith g a (p, dq) n

    g :: (Prob p, dq) -> (Prob p, dq) -> (Prob p, dq)
    g (0, _) (q, v) = (q, v)
    g (p, u) (0, _) = (p, u)
    g (p, u) (q, v) = let pq = p + q in (pq, mix (p / pq) u v)

instance (DeltaQ p t dq, MonadProb p m) => Functor (DeltaQT p t dq m) where
    fmap = liftM

instance (DeltaQ p t dq, MonadProb p m) => Applicative (DeltaQT p t dq m) where
    pure = return
    (<*>) = ap

massiveM :: (DeltaQ p t dq, MonadProb p m) => a -> dq -> m (Maybe (a, dq))
massiveM a dq = case massive dq of
    Nothing         -> return Nothing
    Just (p, dq')
        | p == 1    -> return $ Just (a, dq)
        | otherwise -> coin p (Just (a, dq')) Nothing

instance (DeltaQ p t dq, MonadProb p m) => Monad (DeltaQT p t dq m) where

    return a = DeltaQT $ \dq -> massiveM a dq

    ma >>= cont = DeltaQT $ \dq -> do
        m <- runDeltaQT' ma dq
        case m of
            Nothing       -> return Nothing
            Just (a, dq') -> runDeltaQT' (cont a) dq'

liftQT :: (DeltaQ p t dq, MonadProb p m) => m a -> DeltaQT p t dq m a
liftQT ma = DeltaQT $ \dq -> ma >>= \a -> massiveM a dq

instance (DeltaQ p t dq, MonadProb p m) => MonadProb p (DeltaQT p t dq m) where
    coin 0 _ b = return b
    coin 1 a _ = return a
    coin p a b = DeltaQT $ \dq -> coin p a b >>= \c -> massiveM c dq

instance (DeltaQ p t dq, MonadProb p m) => MonadDeltaQ p t dq (DeltaQT p t dq m) where

    delay dq = DeltaQT $ \dq' -> massiveM () $ dq' <> dq

    x `race` y = DeltaQT $ \dq -> do
        ma <- runDeltaQT' x dq
        mb <- runDeltaQT' y dq
        let dqa = maybe never snd ma
            dqb = maybe never snd mb
        case ftf dqa dqb of
            Never               -> return Nothing
            First  pa dqa'      -> let Just (a, _) = ma
                                   in  coin pa (Just (Left  (a, f mb dqa'), dqa')) Nothing
            Second pb dqb'      -> let Just (b, _) = mb
                                   in  coin pb (Just (Right (b, f ma dqb'), dqb')) Nothing
            Mix pa dqa' pb dqb' -> let Just (a, _) = ma
                                       Just (b, _) = mb
                                   in  coinM (pa + pb)
                                           (coin (pa / (pa + pb))
                                               (Just (Left  (a, f mb dqa'), dqa'))
                                               (Just (Right (b, f ma dqb'), dqb')))
                                           (return Nothing)
      where
        f :: Maybe (c, dq) -> dq -> DeltaQT p t dq m c
        f Nothing _          = DeltaQT $ const $ return Nothing
        f (Just (c, dqc)) dq = case dqc `after` dq of
            Nothing        -> DeltaQT $ const $ return Nothing
            Just (_, dqc') -> DeltaQT $ \dq' -> massiveM c (dqc' `maxDQ` dq')

timing :: (Ord dq, DeltaQ p t dq) => DeltaQM p t dq a -> dq
timing m =
    let (p, dq) = runDeltaQM (void m) M.! ()
    in  mix p dq never
