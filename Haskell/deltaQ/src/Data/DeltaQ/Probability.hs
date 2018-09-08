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
    , mixP
    , MonadProb (..)
    , coinM
    , pick
    , SamplingT (..)
    , sampleIO
    , sample
    , ProbT
    , runProbT
    , ProbM
    , runProbM
    ) where

import           Control.Arrow             (second)
import           Control.Monad.Operational
import           Control.Monad.Random

import           Data.Functor.Identity     (Identity (..))
import           Data.List.NonEmpty        (NonEmpty (..), toList)
import qualified Data.List.NonEmpty        as NE
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as M

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

    elements :: NonEmpty a -> m a
    elements xs = go (NE.length xs) xs
      where
        go :: Int -> NonEmpty a -> m a
        go _ (a :| [])       = return a
        go n (a :| (y : ys)) = do
            let p = prob $ 1 / fromIntegral n
            c <- coin p True False
            if c then return a
                 else go (n - 1) (y :| ys)

coinM :: MonadProb p m => Prob p -> m a -> m a -> m a
coinM p x y = do
    a <- x
    b <- y
    coin p a b

pick :: forall p m a. MonadProb p m => NonEmpty a -> m (a, [a])
pick = elements . picks
  where
    picks :: NonEmpty a -> NonEmpty (a, [a])
    picks (x :| [])           = return (x, [])
    picks (x :| ys@(y : ys')) =
        let zs = toList $ picks $ y :| ys'
            zs' = second (x :) <$> zs
        in  (x, ys) :| zs'

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

data ProbI p a =
      Coin (Prob p) a a
    | Elements (NonEmpty a)
    deriving (Show, Eq, Ord)

newtype ProbT p m a = ProbT (ProgramT (ProbI p) m a)
    deriving (Functor, Applicative, Monad, MonadTrans)

instance (Ord p, Fractional p, Monad m) => MonadProb p (ProbT p m) where
    coin 0 _ y = return y
    coin 1 x _ = return x
    coin p x y = ProbT $ singleton $ Coin p x y

runProbT :: forall p m a .
            (Ord p, Fractional p, Monad m, Ord a)
         => ProbT p m a
         -> m (Map a (Prob p))
runProbT (ProbT u) = viewT u >>= eval
  where
    eval :: ProgramViewT (ProbI p) m a -> m (Map a (Prob p))
    eval (Return a)              = return $ M.singleton a 1
    eval (Coin p x y :>>= cont)  = do
        m <- runProbT $ ProbT $ cont x
        n <- runProbT $ ProbT $ cont y
        return $ M.unionWith (+) ((* p) <$> m) ((* (1 - p)) <$> n)
    eval (Elements xs :>>= cont) = do
        ys <- fmap NE.toList $ forM xs $ runProbT . ProbT . cont
        let f = prob $ recip $ fromIntegral $ NE.length xs
        return $ M.unionsWith (+) $ map (fmap (* f)) ys

type ProbM p = ProbT p Identity

runProbM :: (Ord a, Ord p, Fractional p) => ProbM p a -> Map a (Prob p)
runProbM = runIdentity . runProbT

die :: ProbM Rational Int
die = elements $ 1 :| [2..6]

dice :: Int -> ProbM Rational Int
dice n = sum <$> replicateM n die
