{-# LANGUAGE ScopedTypeVariables #-}

module Data.Piecewise.Charts
    ( layoutCdf
    , layoutPdf
    , layoutPW
    , toFilePW
    ) where

import Control.Lens
import Control.Monad
import Data.Default.Class
import Data.Piecewise
import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Cairo
import Graphics.Rendering.Chart.Grid
import Prelude                                hiding (lines)
import Text.Printf                            (printf)

toDouble :: Real r => r -> Double
toDouble = fromRational . toRational

lines :: forall r. (Ord r, Real r, Fractional r)
      => Int
      -> Piecewise r
      -> PlotLines Double Double
lines n x = plot_lines_values .~ [[getPoint t | t <- times]]
      $ def
  where
    tmin, tmax :: r
    (tmin, tmax) = case pieces x of
        [] -> (0, 1)
        ps -> case (head ps, last ps) of
                (Piece a _ _, Piece _ b _) -> (a, b)

    times :: [r]
    times =
        let delta = (tmax - tmin) / fromIntegral n
        in  [tmin + delta * fromIntegral i | i <- [0 .. n]]

    getPoint :: r -> (Double, Double)
    getPoint t = (toDouble t, toDouble $ evalPW t x)

mean :: (Real r, Fractional r) => Piecewise r -> Plot Double Double
mean dq = case pieces dq of
    [] -> toPlot $ PlotHidden [] []
    _  ->
        let m = toDouble $ meanPW dq
            s = printf "mean %6.4f" m
        in  vlinePlot s def m

layoutCdf :: (Ord r, Real r, Fractional r) => Int -> Piecewise r -> Layout Double Double
layoutCdf n dq = layout_title .~ "ΔQ (cdf)"
               $ layout_plots .~ [ toPlot $ lines n $ cdfPW dq
                                 , mass
                                 , mean dq
                                 ]
               $ def
  where
    m :: Double
    m = toDouble $ intPW dq

    mass :: Plot Double Double
    mass =
        let s = printf "mass %6.4f" m
        in  hlinePlot s def m

layoutPdf :: (Ord r, Real r, Fractional r) => Int -> Piecewise r -> Layout Double Double
layoutPdf n dq = layout_title .~ "ΔQ (pdf)"
               $ layout_plots .~ [ toPlot $ lines n dq
                                 , mean dq
                                 ]
               $ def

layoutPW :: (Ord r, Real r, Fractional r)
         => Int
         -> Piecewise r
         -> Grid (Renderable (LayoutPick Double Double Double))
layoutPW n dq = layoutToGrid (layoutCdf n dq) ./. layoutToGrid (layoutPdf n dq)

toFilePW :: (Ord r, Real r, Fractional r) => FilePath -> Piecewise r -> IO ()
toFilePW fp = void
            . renderableToFile def fp
            . fillBackground def
            . toRenderable . layoutPW 1000
