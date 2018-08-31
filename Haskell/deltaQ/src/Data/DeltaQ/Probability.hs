{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Data.DeltaQ.Probability
    ( Prob (getProb)
    , prob
    , mixP
    , MonadProb (..)
    , coinM
    , elements
    , SamplingT (..)
    , sampleIO
    , sample
    , ProbT
    , runProbT
    , ProbM
    , runProbM
    ) where

import           Control.Monad
import           Control.Monad.Random

import           Data.Functor.Identity (Identity (..))
import           Data.List.NonEmpty    (NonEmpty (..))
import qualified Data.List.NonEmpty    as NE
import           Data.Map.Strict       (Map)
import qualified Data.Map.Strict       as M

newtype Prob p = Prob {getProb :: p}
    deriving (Eq, Ord)

instance Show p => Show (Prob p) where
    showsPrec d (Prob p) = showsPrec d p

prob :: (Ord p, Num p) => p -> Prob p
prob = Prob . max 0 . min 1

instance (Ord p, Num p) => Num (Prob p) where

    Prob x + Prob y = prob $ x + y

    Prob x * Prob y = prob $ x * y

    abs p = p

    signum p@(Prob 0) = p
    signum   (Prob _) = 1

    fromInteger = prob . fromInteger

    Prob x - Prob y = prob $ x - y

instance (Ord p, Fractional p) => Fractional (Prob p) where

    fromRational = prob . fromRational

    Prob x / Prob y = prob $ x / y

mixP :: (Ord p, Num p) => Prob p -> Prob p -> Prob p -> Prob p
mixP p x y = p * x + (1 - p) * y

class (Ord p, Fractional p, Monad m) => MonadProb p m | m -> p where
    coin :: Prob p -> a -> a -> m a

coinM :: MonadProb p m => Prob p -> m a -> m a -> m a
coinM p x y = do
    a <- x
    b <- y
    coin p a b

elements :: forall p m a. MonadProb p m => NonEmpty a -> m a
elements xs = go (NE.length xs) xs
  where
    go :: Int -> NonEmpty a -> m a
    go _ (a :| [])       = return a
    go n (a :| (y : ys)) = do
        let p = prob $ 1 / fromIntegral n
        c <- coin p True False
        if c then return a
             else go (n - 1) (y :| ys)

instance Monad m => MonadProb Double (RandT StdGen m) where
    coin p x y = runSamplingT $ coin p x y

instance MonadProb Double IO where
    coin p x y = runSamplingT $ coin p x y

newtype SamplingT p m a = SamplingT {runSamplingT :: m a}
    deriving (Functor, Applicative, Monad, MonadRandom)

instance MonadTrans (SamplingT p) where
    lift = SamplingT

instance (Ord p, Fractional p, Random p, MonadRandom m)
         => MonadProb p (SamplingT p m) where
    coin p x y = do
        r <- getRandomR (0, 1)
        return $ if prob r <= p then x else y

sampleIO :: (forall m. MonadProb Double m => m a) -> IO a
sampleIO = id

sample :: Int -> (forall m. MonadProb Double m => m a) -> a
sample seed = (`evalRand` mkStdGen seed)

data ProbT p m a where
    ProbT :: (forall b. Ord b => (a -> m (Map b (Prob p)))
          -> m (Map b (Prob p)))
          -> ProbT p m a

runProbT' :: Ord b => ProbT p m a -> (a -> m (Map b (Prob p))) -> m (Map b (Prob p))
runProbT' (ProbT g) = g

runProbT :: (Ord a, Ord p, Num p, Monad m) => ProbT p m a -> m (Map a (Prob p))
runProbT = flip runProbT' $ \a -> return $ M.singleton a 1

type ProbM p a = ProbT p Identity a

runProbM :: (Ord a, Ord p, Num p) => ProbM p a -> Map a (Prob p)
runProbM = runIdentity . runProbT

instance Monad m => Functor (ProbT p m) where
    fmap = liftM

instance Monad m => Applicative (ProbT p m) where
    pure = return
    (<*>) = ap

instance Monad m => Monad (ProbT p m) where

    return a = ProbT $ \f -> f a

    ma >>= cont = ProbT              $ \f ->
                  runProbT' ma       $ \a ->
                  runProbT' (cont a) f

instance MonadTrans (ProbT p) where

    lift ma = ProbT (ma >>=)

instance (Ord p, Fractional p, Monad m) => MonadProb p (ProbT p m) where
    coin 0 _ b = return b
    coin 1 a _ = return a
    coin p a b = ProbT $ \f -> do
        m <- f a
        n <- f b
        return $ M.unionWith (+) ((* p) <$> m) ((* (1 - p)) <$> n)
