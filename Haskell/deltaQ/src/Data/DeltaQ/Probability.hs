{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Data.DeltaQ.Probability
    ( Prob (getProb)
    , prob
    , MonadProb (..)
    , coinM
    , elements
    , sampleIO
    , sample
    ) where

import           Control.Monad.Random

import           Data.List.NonEmpty   (NonEmpty (..))
import qualified Data.List.NonEmpty   as NE

newtype Prob a = Prob {getProb :: a}
    deriving (Show, Eq, Ord)

prob :: (Num a, Ord a) => a -> Prob a
prob = Prob . max 0 . min 1

class (Ord a, Num a, Fractional a, Monad m) => MonadProb a m | m -> a where
    coin :: Prob a -> b -> b -> m b

coinM :: MonadProb a m => Prob a -> m b -> m b -> m b
coinM p x y = do
    a <- x
    b <- y
    coin p a b

elements :: forall a m b. MonadProb a m => NonEmpty b -> m b
elements xs = go (NE.length xs) xs
  where
    go :: Int -> NonEmpty b -> m b
    go _ (b :| [])       = return b
    go n (b :| (y : ys)) = do
        let p = prob $ recip $ fromIntegral n
        c <- coin p True False
        if c then return b
             else go (n - 1) (y :| ys)

instance Monad m => MonadProb Double (RandT StdGen m) where
    coin p x y = runSamplingT $ coin p x y

instance MonadProb Double IO where
    coin p x y = runSamplingT $ coin p x y

newtype SamplingT a m b = SamplingT {runSamplingT :: m b}
    deriving (Functor, Applicative, Monad, MonadRandom)

instance MonadTrans (SamplingT a) where
    lift = SamplingT

instance (Ord a, Num a, Fractional a, Random a, MonadRandom m)
         => MonadProb a (SamplingT a m) where
    coin p x y = do
        r <- getRandomR (0, 1)
        return $ if r <= getProb p then x else y

sampleIO :: (forall m. MonadProb Double m => m a) -> IO a
sampleIO = id

sample :: Int -> (forall m. MonadProb Double m => m a) -> a
sample seed = (`evalRand` mkStdGen seed)
