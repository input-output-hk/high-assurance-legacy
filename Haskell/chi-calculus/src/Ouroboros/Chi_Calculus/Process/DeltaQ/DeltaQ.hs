{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Ouroboros.Chi_Calculus.Process.DeltaQ.DeltaQ
    ( Seconds
    , DeltaQ (..)
    , split
    , MonadDeltaQ (..)
    , Sampling (..)
    ) where

import Control.Monad.Random (MonadRandom (..), fromList)
import Data.List.NonEmpty   (NonEmpty (..), toList)

type Seconds = Double

data DeltaQ = Uniform Seconds Seconds
    deriving Show

class Monad m => MonadDeltaQ m where
    deltaQM  :: DeltaQ -> m (Maybe Seconds)
    elements :: NonEmpty a -> m a

split :: MonadDeltaQ m => NonEmpty a -> m (a, Maybe (NonEmpty a))
split = elements . allSplits
  where
    allSplits :: NonEmpty a -> NonEmpty (a, Maybe (NonEmpty a))
    allSplits (a :| [])          = (a, Nothing) :| []
    allSplits (a :| xs@(y : ys)) = (a, Just (y :| ys)) :| [(z, Just (a :| zs)) | (z, zs) <- allSplits' xs]

    allSplits' :: [a] -> [(a, [a])]
    allSplits' []       = []
    allSplits' (x : xs) = (x, xs) : [(y, x : ys) | (y, ys) <- allSplits' xs]

newtype Sampling m a = Sampling {runSampling :: m a}
    deriving (Functor, Applicative, Monad)

instance MonadRandom m => MonadDeltaQ (Sampling m) where

    deltaQM (Uniform t1 t2) = do
        let t1' = max 0 t1
            t2' = max 0 t2
        case compare t1' t2' of
            EQ -> return $ Just t1'
            GT -> return Nothing
            LT -> Just <$> Sampling (getRandomR (t1', t2'))

    elements xs = Sampling $ fromList [(x, 1) | x <- toList xs]
