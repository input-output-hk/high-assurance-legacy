{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Distribution
Description : (discrete) probability distributions
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module contains a class and two implementations
for (discrete) probability distributions.
-}

module Distribution
    ( Time
    , Distribution (..)
    , dirac
    , miracle
    , defaultMempty
    , defaultMappend
    , Dist (..)
    , NDist (..)
    , DTime
    , distToPNG
    , sampleDist
    ) where

import           Control.Monad                          (void)
import           Control.Monad.Random                   (MonadRandom (..))
import           Data.List                              (foldl')
import           Data.List.NonEmpty                     (NonEmpty (..), fromList, toList)
import           Data.Map.Strict                        (Map)
import qualified Data.Map.Strict                        as M
import           Data.Monoid                            ((<>))
import           Graphics.Rendering.Chart.Easy
import           Graphics.Rendering.Chart.Backend.Cairo
import           Numeric.Natural
import           Probability
import           WeightedChoice

-- | Time is simply represented by a natural number,
-- so we only consider /discrete/ time.
type Time = Natural

instance Monoid Time where
    mempty  = 0
    mappend = (+)

-- | A class for probability distributions @d@ of values of type @a@.
class WeightedChoice d => Distribution d a | d -> a where

    -- | Converts a distribution into a non-empty list of value-probability
    -- pairs. The probabilities are all non-zero, and their sum is one.
    toDiracs   :: d -> NonEmpty (a, Probability)

    -- | Takes a non-empty list of value-probability pairs (non-zero
    -- probabilities with sum one) and converts it into a distribution.
    fromDiracs :: NonEmpty (a, Probability) -> d

-- | @'dirac' a@ is the distribution of value @a@ with probability one.
dirac :: Distribution d a => a -> d
dirac a = fromDiracs $ (a, 1) :| []

-- | The time-distribution with time zero and probability one.
miracle :: Distribution d Time => d
miracle = dirac 0

-- | A helper function to implement @'mempty'@ for a @'Monoid'@-instance for
-- distributions of monoidal values.
defaultMempty :: (Distribution d a, Monoid a) => d
defaultMempty = dirac mempty

-- | A helper function to implement @'mappend'@ for a @'Monoid'@-instance for
-- distributions of monoidal values.
defaultMappend :: forall a d. (Distribution d a, Monoid a) => d -> d -> d
defaultMappend d e =
    let x :| xs         = toDiracs d
        y :| ys         = toDiracs e
    in  fromDiracs $ f x y :| ([f x y'  | y' <- ys] ++
                               [f x' y' | x' <- xs, y' <- y : ys])
  where
    f :: (a, Probability) -> (a, Probability) -> (a, Probability)
    f (a, p) (b, q) = (a <> b, p * q)

-- | Represents distributions as non-empty lists of value-probability
-- pairs (with non-zero probabilities that sum to one).
-- This can be used for any Haskell type.
newtype Dist a = Dist (NonEmpty (a, Probability))
    deriving Show

instance WeightedChoice (Dist a) where
    weightedChoice 0 _                y                = y
    weightedChoice 1 x                _                = x
    weightedChoice p (Dist (x :| xs)) (Dist (y :| ys)) = 
        let q = 1 - p
        in  Dist $ f p x :| map (f p) xs ++ f q y : map (f q) ys
      where 
        f :: Probability -> (a, Probability) -> (a, Probability)
        f s (a, q) = (a, s * q) 

instance Distribution (Dist a) a where
    fromDiracs         = Dist
    toDiracs (Dist xs) = xs

instance Monoid a => Monoid (Dist a) where
    mempty  = defaultMempty
    mappend = defaultMappend

-- | Represents distributions as non-empty maps from values
-- to (non-zero) probabilities (that sum to one).
-- This can only be used for Haskell types that have an
-- @'Ord'@-instance.
newtype NDist a = NDist (Map a Probability)
    deriving (Show, Eq, Ord)

instance Ord a => WeightedChoice (NDist a) where
    weightedChoice 0 _         y         = y
    weightedChoice 1 x         _         = x
    weightedChoice p (NDist m) (NDist n) =
        let q  = (1 - p)
            xs = [(a, s * p) | (a, s) <- M.toList m]
            ys = [(a, s * q) | (a, s) <- M.toList n]
        in  NDist $ foldl' f M.empty $ xs ++ ys
      where
        f :: Map a Probability -> (a, Probability) -> Map a Probability
        f m' (a, s) = M.insertWith (+) a s m'

instance Ord a => Distribution (NDist a) a where

    toDiracs (NDist m) = fromList $ M.toList m

    fromDiracs ((a, p) :| xs) = NDist $ foldl' f (M.singleton a p) xs
      where
        f :: Map a Probability -> (a, Probability) -> Map a Probability
        f m (b, q) = M.insertWith (+) b q m

instance (Ord a, Monoid a) => Monoid (NDist a) where
    mempty  = defaultMempty
    mappend = defaultMappend

-- | Distributions of @'Time'@.
type DTime = NDist Time

plotDist :: Probability -> DTime -> Plot Double Double
plotDist p d = plotBars $ plot_bars_values .~ xs
                        $ plot_bars_titles .~ ["tangible: " ++ show (probToDouble p)]
                        $ def
  where
    xs :: [(Double, [Double])]
    xs = [ (fromIntegral n, [probToDouble $ p * q])
         | (n, q) <- toList $ toDiracs d
         ]

layoutDist :: Probability -> DTime -> Layout Double Double
layoutDist p d = layout_plots                .~ [plotDist p d]
               $ layout_x_axis . laxis_title .~ "time"
               $ layout_y_axis . laxis_title .~ "probability"
               $ def

-- | Creates a PNG-image of a (possibly intangible) time-distribution.
distToPNG :: Probability -- ^ tangible mass
          -> DTime       -- ^ (tangible) time-distribution
          -> FilePath    -- ^ target file
          -> IO ()
distToPNG p d f = void $ renderableToFile def f $ toRenderable $ layoutDist p d

-- | Samples from a distribution.
sampleDist :: forall m d a. (MonadRandom m, Distribution d a) => d -> m a
sampleDist d = do
    x <- getRandomR (0, 1)
    go x $ toDiracs d
  where
    go :: Double -> NonEmpty (a, Probability) -> m a
    go _  ((a, _) :| [])       = return a
    go !x ((a, p) :| (y : ys)) =
        let p' = probToDouble p
        in  if x <= p' then return a
                       else go (x - p') $ y :| ys
