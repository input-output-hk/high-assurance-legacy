{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Data.DeltaQ.Monad
    ( MonadDeltaQ (..)
    , SamplingDQT (..)
    , DeltaQT
    , runDeltaQT
    , runDeltaQM
    , timing
    , after'
    ) where

import           Control.Monad
import           Control.Monad.Random      hiding (uniform)
import           Control.Monad.Trans.Class (MonadTrans (..))
import           Data.DeltaQ.Core
import           Data.DeltaQ.Probability
import           Data.Functor.Identity     (Identity (..))
import           Data.List                 (foldl')
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as M

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

newtype DeltaQT p t dq m a = DeltaQT {runDeltaQT' :: dq -> m (a, dq)}

runDeltaQT :: DeltaQ p t dq => DeltaQT p t dq m a -> m (a, dq)
runDeltaQT m = runDeltaQT' m mempty

type DeltaQM p t dq a = DeltaQT p t dq (ProbT p Identity) a

runDeltaQM :: forall a p t dq. (Ord a, DeltaQ p t dq, Ord dq)
           => DeltaQM p t dq a
           -> Map a (Prob p, dq)
runDeltaQM x = foldl' f M.empty $ M.toList m
  where
    m :: Map (a, dq) (Prob p)
    m = runProbM $ runDeltaQT x

    f :: Map a (Prob p, dq)
      -> ((a, dq), Prob p)
      -> Map a (Prob p, dq)
    f n ((a, dq), p) = M.insertWith g a (p, dq) n

    g :: (Prob p, dq) -> (Prob p, dq) -> (Prob p, dq)
    g (0, _) (q, v) = (q, v)
    g (p, u) (0, _) = (p, u)
    g (p, u) (q, v) = let pq = p + q in (pq, mix (p / pq) u v)

instance (DeltaQ p t dq, Monad m) => Functor (DeltaQT p t dq m) where
    fmap = liftM

instance (DeltaQ p t dq, Monad m) => Applicative (DeltaQT p t dq m) where
    pure = return
    (<*>) = ap

instance (DeltaQ p t dq, Monad m) => Monad (DeltaQT p t dq m) where

    return a = DeltaQT $ \dq -> return (a, dq)

    ma >>= cont = DeltaQT $ \dq -> do
        (a, dq') <- runDeltaQT' ma dq
        runDeltaQT' (cont a) dq'

instance DeltaQ p t dq => MonadTrans (DeltaQT p t dq) where
    lift ma = DeltaQT $ \dq -> (\a -> (a, dq)) <$> ma

instance (DeltaQ p t dq, MonadProb p m) => MonadProb p (DeltaQT p t dq m) where
    coin p a b = DeltaQT $ \dq -> coin p (a, dq) (b, dq)

instance (DeltaQ p t dq, MonadProb p m) => MonadDeltaQ p t dq (DeltaQT p t dq m) where

    delay dq = DeltaQT $ \dq' -> return ((), dq' <> dq)

    x `race` y = DeltaQT $ \dq -> do
        (a, dqa) <- runDeltaQT' x dq
        (b, dqb) <- runDeltaQT' y dq
        case ftf dqa dqb of
            First  dqa' _       -> return (Left  (a, f b dqb dqa'), dqa')
            Second dqb' _       -> return (Right (b, f a dqa dqb'), dqb')
            Mix p dqa' _ dqb' _ -> coin p
                (Left  (a, f b dqb dqa'), dqa')
                (Right (b, f a dqa dqb'), dqb')
      where
        f :: c -> dq -> dq -> DeltaQT p t dq m c
        f c dq1 dq2 =
            let Just dq  = dq1 `after'` dq2
            in  returnAt c dq

timing :: (Ord dq, DeltaQ p t dq) => DeltaQM p t dq a -> dq
timing m = snd $ runDeltaQM (void m) M.! ()

after' :: DeltaQ p t dq => dq -> dq -> Maybe dq
after' dq1 dq2 = smear dq2 (dq1 `after`)

at :: forall p t dq. DeltaQ p t dq => dq -> dq -> dq
at dq1 dq2 = let Just dq = smear dq2 f in dq
  where
    f :: Maybe t -> Maybe dq
    f mt = smear dq1 $ g mt

    g :: Maybe t -> Maybe t -> Maybe dq
    g mt ms = Just $ case (ms, mt) of
        (Just s, Just t) -> exact (max s t)
        _                -> never

returnAt :: (DeltaQ p t dq, Monad m) => a -> dq -> DeltaQT p t dq m a
returnAt a dq = DeltaQT $ \dq' -> return (a, dq `at` dq')
