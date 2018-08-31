{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Data.DeltaQ.Monad
    ( MonadDeltaQ (..)
    , SamplingDQT (..)
    , DeltaQT (..)
    , runDeltaQM
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
import           Data.Proxy                (Proxy (..))

class (DeltaQ p t dq, MonadProb p m) => MonadDeltaQ p t dq m | m -> p t dq where
    impossible :: m a
    delay      :: dq -> m ()
    race       :: m a -> m b -> m (Either (a, m b) (b, m a))

newtype SamplingDQT p t dq m a =
    SamplingDQT {runSamplingDQT :: SamplingT p m (Maybe (a, t))}

instance (DeltaQ p t dq, Monad m) => Functor (SamplingDQT p t dq m) where
    fmap = liftM

instance (DeltaQ p t dq, Monad m) => Applicative (SamplingDQT p t dq m) where
    pure = return
    (<*>) = ap

instance (DeltaQ p t dq, Monad m) => Monad (SamplingDQT p t dq m) where

    return x = SamplingDQT $ return $ Just (x, mempty)

    ma >>= cont = SamplingDQT $ do
        x <- runSamplingDQT ma
        case x of
            Nothing     -> return Nothing
            Just (a, s) -> do
                y <- runSamplingDQT $ cont a
                case y of
                    Nothing     -> return Nothing
                    Just (b, t) -> return $ Just (b, s <> t)

instance (DeltaQ p t dq, Random p, MonadRandom m) =>
         MonadProb p (SamplingDQT p t dq m) where
    coin p x y = SamplingDQT $ coin p (Just (x, mempty)) (Just (y, mempty))

instance forall p t dq m. (DeltaQ p t dq, Random p, MonadRandom m) =>
         MonadDeltaQ p t dq (SamplingDQT p t dq m) where

    impossible = SamplingDQT $ return Nothing

    delay dq = SamplingDQT $ do
        mt <- sampleDQ dq
        case mt of
            Nothing -> return Nothing
            Just t  -> return $ Just ((), t)

    race x y = SamplingDQT $ do
        mx <- runSamplingDQT x
        my <- runSamplingDQT y
        let sb = sub (Proxy :: Proxy dq)
        case (mx, my) of
            (Nothing, Nothing)         ->
                    return Nothing
            (Just (a, s), Nothing)     ->
                    return $ Just (Left (a, SamplingDQT $ return Nothing), s)
            (Nothing, Just (b, t))     ->
                    return $ Just (Right (b, SamplingDQT $ return Nothing), t)
            (Just (a, s), Just (b, t))
                | s < t                ->
                    return $ Just (Left (a, SamplingDQT $ return $ Just (b, sb t s)), s)
                | t < s                ->
                    return $ Just (Right (b, SamplingDQT $ return $ Just (a, sb s t)), t)
                | otherwise            ->
                    coin 0.5
                        (Just (Left  (a, SamplingDQT $ return $ Just (b, mempty)), s))
                        (Just (Right (b, SamplingDQT $ return $ Just (a, mempty)), s))

newtype DeltaQT p t dq m a = DeltaQT {runDeltaQT :: dq -> m (Maybe (a, dq))}

type DeltaQM p t dq a = DeltaQT p t dq (ProbT p Identity) a

runDeltaQM :: forall a p t dq. (Ord a, DeltaQ p t dq, Ord dq)
           => DeltaQM p t dq a
           -> dq
           -> Map a (Prob p, dq)
runDeltaQM x dq = foldl' f M.empty $ M.toList m
  where
    m :: Map (Maybe (a, dq)) (Prob p)
    m = runProbM $ runDeltaQT x dq

    f :: Map a (Prob p, dq)
      -> (Maybe (a, dq), Prob p)
      -> Map a (Prob p, dq)
    f n (Nothing      , _) = n
    f n (Just (a, dq'), p) = M.insertWith g a (p, dq') n

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

    return a = DeltaQT $ \dq -> return $ Just (a, dq)

    ma >>= cont = DeltaQT $ \dq -> do
        x <- runDeltaQT ma dq
        case x of
            Nothing       -> return Nothing
            Just (a, dq') -> runDeltaQT (cont a) dq'

instance DeltaQ p t dq => MonadTrans (DeltaQT p t dq) where
    lift ma = DeltaQT $ \dq -> (\a -> Just (a, dq)) <$> ma

instance (DeltaQ p t dq, MonadProb p m) => MonadProb p (DeltaQT p t dq m) where
    coin p a b = DeltaQT $ \dq -> coin p (Just (a, dq)) (Just (b, dq))

instance (DeltaQ p t dq, MonadProb p m) => MonadDeltaQ p t dq (DeltaQT p t dq m) where

    impossible = DeltaQT $ const $ return Nothing

    delay dq = DeltaQT $ \dq' -> return $ Just ((), dq' <> dq)

    x `race` y = DeltaQT $ \dq -> do
        m <- runDeltaQT x dq
        n <- runDeltaQT y dq
        case (m, n) of
            (Just (a, dqa), Just (b, dqb)) -> case ftf dqa dqb of
                First  dqa' _       -> return $ Just (Left  (a, returnAt b dqb), dqa')
                Second dqb' _       -> return $ Just (Right (b, returnAt a dqa), dqb')
                Mix p dqa' _ dqb' _ -> coin p
                    (Just (Left  (a, returnAt b dqb), dqa'))
                    (Just (Right (b, returnAt a dqa), dqb'))
            _                              -> return Nothing

returnAt :: (DeltaQ p t dq, Monad m) => a -> dq -> DeltaQT p t dq m a
returnAt a dq = DeltaQT $ \dq' -> return $ case dq `after'` dq' of
    Nothing   -> Nothing
    Just dq'' -> Just (a, dq'')
  where
    after' dq1 dq2 = smear dq2 (dq1 `after`)
