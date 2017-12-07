{-# OPTIONS_GHC -fno-warn-orphans #-}

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
    ) where

import           Control.Monad                          (void)
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

type Time = Natural

instance Monoid Time where
    mempty  = 0
    mappend = (+)

class WeightedChoice d => Distribution d a | d -> a where
    toDiracs   :: d -> NonEmpty (a, Probability)
    fromDiracs :: NonEmpty (a, Probability) -> d

dirac :: Distribution d a => a -> d
dirac a = fromDiracs $ (a, 1) :| []

miracle :: Distribution d Time => d
miracle = dirac 0

defaultMempty :: (Distribution d a, Monoid a) => d
defaultMempty = dirac mempty

defaultMappend :: forall a d. (Distribution d a, Monoid a) => d -> d -> d
defaultMappend d e =
    let x :| xs         = toDiracs d
        y :| ys         = toDiracs e
    in  fromDiracs $ f x y :| ([f x y'  | y' <- ys] ++
                               [f x' y' | x' <- xs, y' <- y : ys])
  where
    f :: (a, Probability) -> (a, Probability) -> (a, Probability)
    f (a, p) (b, q) = (a <> b, p * q)

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

distToPNG :: Probability -> DTime -> FilePath -> IO ()
distToPNG p d f = void $ renderableToFile def f $ toRenderable $ layoutDist p d
