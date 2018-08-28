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
    , impossibleP
    , certainP
    , isImpossibleP
    , isCertainP
    , complementP
    , mixP
    , mulP
    , addP
    , recipP
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
    deriving (Eq, Ord)

instance Show a => Show (Prob a) where
    showsPrec d (Prob a) = showsPrec d a

prob :: (Ord a, Num a) => a -> Prob a
prob = Prob . max 0 . min 1

impossibleP, certainP :: (Ord a, Num a) => Prob a
impossibleP = prob 0
certainP = prob 1

isImpossibleP, isCertainP :: (Eq a, Num a) => Prob a -> Bool
isImpossibleP (Prob p) = p == 0
isCertainP    (Prob p) = p == 1

complementP :: (Ord a, Num a) => Prob a -> Prob a
complementP (Prob p) = prob (1 - p)

mixP :: (Ord a, Num a) => Prob a -> Prob a -> Prob a -> Prob a
mixP (Prob p) (Prob x) (Prob y) = prob (p * x + (1 - p) * y)

mulP :: (Ord a, Num a) => Prob a -> Prob a -> Prob a
mulP p q = mixP p q impossibleP

addP :: (Ord a, Num a) => Prob a -> Prob a -> Prob a
addP (Prob p) (Prob q) = prob (p + q)

recipP :: (Ord a, Fractional a) => Prob a -> Maybe (Prob a)
recipP (Prob 0) = Nothing
recipP (Prob p) = Just $ prob $ recip p

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
