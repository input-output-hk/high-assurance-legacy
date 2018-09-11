module Charts
    ( layoutCdf
    , layoutPdf
    , layoutDDQ
    , toFileDDQ
    ) where

import Control.Lens
import Control.Monad
import Data.Default.Class
import Data.DeltaQ
import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Cairo
import Graphics.Rendering.Chart.Grid
import Text.Printf                            (printf)

layoutCdf :: (Show p, Ord p, Fractional p, Real p) => DDQ p IntP -> Layout Int Double

layoutCdf dq = layout_title .~ "ΔQ (cdf)"
             $ layout_plots .~ [ plotBars bars
                               , line
                               ]
             $ def
  where
    m :: Double
    m = fromRational $ toRational $ getProb $ mass dq

    ps :: [Double]
    ps = map (fromRational . toRational . getProb) $ cdf dq

    line :: Plot Int Double
    line =
        let s = printf "mass %6.4f" m
        in  hlinePlot s def m

    bars :: PlotBars Int Double
    bars = plot_bars_values .~ zipWith (\t p -> (t, [p])) [0..] ps
         $ def

layoutPdf :: (Ord p, Fractional p, Real p) => DDQ p IntP -> Layout Int Double
layoutPdf dq = layout_title .~ "ΔQ (pdf)"
             $ layout_plots .~ [ plotBars bars ]
             $ def
  where
    ps :: [Double]
    ps = map (fromRational . toRational . getProb) $ pdf dq

    bars :: PlotBars Int Double
    bars = plot_bars_values .~ zipWith (\t p -> (t, [p])) [0..] ps
         $ def

layoutDDQ :: (Show p, Ord p, Fractional p, Real p)
          => DDQ p IntP
          -> Grid (Renderable (LayoutPick Int Double Double))
layoutDDQ dq = layoutToGrid (layoutCdf dq) ./. layoutToGrid (layoutPdf dq)

toFileDDQ :: (Show p, Ord p, Fractional p, Real p) => FilePath -> DDQ p IntP -> IO ()
toFileDDQ fp = void . renderableToFile def fp . fillBackground def . toRenderable . layoutDDQ
