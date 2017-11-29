module Distribution
    ( Distribution (..)
    , miracle
    , between
    , weighted
    , DSample (..)
    , DAbstract (..)
    , toAbstract
    , fromAbstract
    , sampleIO
    ) where

import Control.Monad.State
import System.Random
import Time

class Distribution a where
    convolve :: a -> a -> a
    choice   :: Rational -> a -> a -> a
    dirac    :: Seconds -> a
    uniform  :: Seconds -> a

miracle :: Distribution a => a
miracle = dirac 0

between :: Distribution a => Seconds -> Seconds -> a
between s t
    | s > t     = error "between: second argument greater than first argument"
    | s == t    = dirac s
    | otherwise = dirac s `convolve` uniform (t - s)

weighted :: Distribution a => [(Rational, a)] -> a
weighted []            = miracle
weighted ((a, x) : xs) =
    let b = sum $ map fst xs
        y = weighted xs
    in  if a + b == 0 then miracle
                      else choice (a / (a + b)) x y

newtype DSample = DSample {sample :: State StdGen Seconds}

instance Distribution DSample where

    convolve x y = DSample $ (+) <$> sample x <*> sample y
    choice p x y = DSample $ do
        r <- rr
        if r <= p then sample x else sample y
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
    | Choice Rational DAbstract DAbstract
    | Dirac Seconds
    | Uniform Seconds
    deriving Show

simplify :: DAbstract -> DAbstract
simplify (Convolve x y) = case (simplify x, simplify y) of
    (Dirac 0, z)       -> z
    (z, Dirac 0)       -> z
    (Dirac s, Dirac t) -> Dirac (s + t)
    (u, v)             -> Convolve u v
simplify (Choice 1 x _) = simplify x
simplify (Choice 0 _ x) = simplify x
simplify (Choice p x y) = Choice p (simplify x) (simplify y)                
simplify (Uniform 0)    = Dirac 0
simplify x              = x

instance Distribution DAbstract where
    convolve x y = simplify $ Convolve x y
    choice p x y = simplify $ Choice p x y
    dirac = simplify . Dirac
    uniform = simplify . Uniform

toAbstract :: (forall a. Distribution a => a) -> DAbstract
toAbstract = id

fromAbstract :: Distribution a => DAbstract -> a
fromAbstract (Convolve x y) = convolve (fromAbstract x) (fromAbstract y)
fromAbstract (Choice p x y) = choice p (fromAbstract x) (fromAbstract y)
fromAbstract (Dirac s)      = dirac s
fromAbstract (Uniform s)    = uniform s

sampleIO :: (forall a. Distribution a => a) -> IO Seconds
sampleIO = getStdRandom . runState . sample
