module Distribution
    ( Distribution (..)
    , miracle
    , between
    , weighted'
    , DSample (..)
    , DAbstract (..)
    , toAbstract
    , fromAbstract
    , sampleIO
    ) where

import Control.Monad.State
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Monoid
import Probability
import System.Random
import Time
import WeightedChoice

class (Monoid a, WeightedChoice a) => Distribution a where
    dirac    :: Seconds -> a
    uniform  :: Seconds -> a

miracle :: Distribution a => a
miracle = dirac 0

between :: Distribution a => Seconds -> Seconds -> a
between s t
    | s > t     = error "between: second argument greater than first argument"
    | s == t    = dirac s
    | otherwise = dirac s <> uniform (t - s)

weighted' :: Distribution a => [(Rational, a)] -> a
weighted' []            = miracle
weighted' ((a, x) : xs) = weighted $ (a, x) :| xs

newtype DSample = DSample {sample :: State StdGen Seconds}

instance Monoid DSample where
    mempty      = dirac 0
    mappend x y = DSample $ (+) <$> sample x <*> sample y

instance WeightedChoice DSample where
    weightedChoice p x y = DSample $ do
        r <- rr
        if probability r <= p then sample x else sample y

instance Distribution DSample where
    dirac s = DSample $ return s
    uniform s = DSample $ (fromRational . (* toRational s)) <$> rr

rr :: State StdGen Rational
rr = do
    g <- get
    let (x, g') = randomR (0, 1) g :: (Double, StdGen)
    put g'
    return $ toRational x

data DAbstract =
      Convolve DAbstract DAbstract
    | Choice Probability DAbstract DAbstract
    | Dirac Seconds
    | Uniform Seconds
    deriving Show

instance Monoid DAbstract where
    mempty  = Dirac 0
    mappend = Convolve

instance WeightedChoice DAbstract where
    weightedChoice = Choice

instance Distribution DAbstract where
    dirac = Dirac
    uniform = Uniform

toAbstract :: (forall a. Distribution a => a) -> DAbstract
toAbstract = id

fromAbstract :: Distribution a => DAbstract -> a
fromAbstract (Convolve x y) = fromAbstract x <> fromAbstract y
fromAbstract (Choice p x y) = weightedChoice p (fromAbstract x) (fromAbstract y)
fromAbstract (Dirac s)      = dirac s
fromAbstract (Uniform s)    = uniform s

sampleIO :: (forall a. Distribution a => a) -> IO Seconds
sampleIO = getStdRandom . runState . sample
