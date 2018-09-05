module Charts
    ( layoutDDQ
    , toFileDDQ
    ) where

import Control.Lens
import Control.Monad
import Data.Default.Class
import Data.DeltaQ
import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Cairo
import Text.Printf                            (printf)

layoutDDQ :: (Ord p, Fractional p, Real p) => DDQ p IntP -> Layout Int Double
layoutDDQ dq = layout_title .~ "ΔQ"
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

toFileDDQ :: (Ord p, Fractional p, Real p) => FilePath -> DDQ p IntP -> IO ()
toFileDDQ fp = void . renderableToFile def fp . toRenderable . layoutDDQ

test :: IO ()
test = do
    let dq1 = uniform (intP 2) (intP 10) :: DDQ Rational IntP
        dq  = dq1 <> dq1 <> dq1
    toFileDDQ "test.png" dq
