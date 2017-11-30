module Distribution
    ( Dist
    , dirac
    , miracle
    , diracs
    , distToPNG
    ) where

import           Control.Monad                          (void)
import           Data.List                              (foldl')
import           Data.List.NonEmpty                     (NonEmpty (..), fromList, toList)
import           Data.Map.Strict                        (Map)
import qualified Data.Map.Strict                        as M
import           Graphics.Rendering.Chart.Easy
import           Graphics.Rendering.Chart.Backend.Cairo
import           Numeric.Natural
import           Probability
import           WeightedChoice

newtype Dist = Dist (Map Natural Probability)
    deriving (Show, Eq, Ord)

dirac :: Natural -> Dist
dirac n = Dist $ M.singleton n 1

miracle :: Dist
miracle = dirac 0

instance Monoid Dist where
    mempty                   = miracle
    Dist m `mappend` Dist m' = Dist $ foldl' f M.empty
        [ (n + n', p * p')
        | (n, p)   <- M.toList m
        , (n', p') <- M.toList m'
        ]
      where
        f :: Map Natural Probability -> (Natural, Probability) -> Map Natural Probability
        f m'' (n, p) = M.insertWith (+) n p m''

instance WeightedChoice Dist where

    neutral = miracle

    weightedChoice 0 _        x         = x
    weightedChoice 1 x        _         = x
    weightedChoice p (Dist m) (Dist m') = Dist $
        M.unionWith (+) (M.map (* p) m) (M.map (* (1 - p)) m')

diracs :: Dist -> NonEmpty (Natural, Probability)
diracs (Dist m) = fromList $ M.toList m

plotDist :: Probability -> Dist -> Plot Double Double
plotDist p d = plotBars $ plot_bars_values .~ xs
                        $ plot_bars_titles .~ ["tangible: " ++ show (probToDouble p)]
                        $ def
  where
    xs :: [(Double, [Double])]
    xs = [ (fromIntegral n, [probToDouble $ p * q]) 
         | (n, q) <- toList $ diracs d
         ]

layoutDist :: Probability -> Dist -> Layout Double Double
layoutDist p d = layout_plots                .~ [plotDist p d]
               $ layout_x_axis . laxis_title .~ "time"
               $ layout_y_axis . laxis_title .~ "probability"
               $ def

distToPNG :: Probability -> Dist -> FilePath -> IO ()
distToPNG p d f = void $ renderableToFile def f $ toRenderable $ layoutDist p d
