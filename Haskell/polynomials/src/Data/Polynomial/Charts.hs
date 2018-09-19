{-# LANGUAGE ScopedTypeVariables #-}

module Data.Polynomial.Charts
    ( layoutCdf
    , layoutPdf
    , layoutMixed
    , toFileMixed
    ) where

import Control.Lens
import Control.Monad
import Data.Colour
import Data.Colour.Names
import Data.Default.Class
import Data.Maybe                             (fromMaybe)
import Data.Polynomial.Class
import Data.Polynomial.Mixed
import Graphics.Rendering.Chart               hiding (scale, xx, xy)
import Graphics.Rendering.Chart.Backend.Cairo
import Graphics.Rendering.Chart.Grid
import Prelude                                hiding (lines)
import Text.Printf                            (printf)

toDouble :: Real r => r -> Double
toDouble = fromRational . toRational

linesCdf :: forall p t d. (Real t, QAlg t, Distribution p t d)
      => Int
      -> d
      -> PlotLines Double Double
linesCdf n d = lines n d $ cdf d

lines :: forall p t d. (Real t, QAlg t, Distribution p t d)
      => Int
      -> d
      -> (t -> t)
      -> PlotLines Double Double
lines n d f = plot_lines_values .~ [[getPoint t | t <- times]]
      $ def
  where
    tmin, tmax :: t
    (tmin, tmax) = fromMaybe (0, 1) $ support d

    times :: [t]
    times =
        let delta = (tmax - tmin) * fromQ (recip $ fromIntegral n)
        in  [tmin + delta * fromIntegral i | i <- [0 .. n]]

    getPoint :: t -> (Double, Double)
    getPoint t = (toDouble t, toDouble $ f t)

mean' :: (Real t, QAlg t, Distribution p t d) => d -> Plot Double Double
mean' dq = case mean dq of
    Nothing -> toPlot $ PlotHidden [] []
    Just m  -> let m' = toDouble m
                   s  = printf "mean %6.4f" m'
               in  vlinePlot s (line_color .~ opaque red $ def) m'

layoutCdf :: (Real p, QAlg t, Real t, Distribution p t d)
          => Int
          -> d
          -> Layout Double Double
layoutCdf n dq = layout_title .~ "ΔQ (cdf)"
               $ layout_plots .~ [ toPlot $ linesCdf n dq
                                 , mass'
                                 , mean' dq
                                 ]
               $ def
  where
    m :: Double
    m = toDouble $ mass dq

    mass' :: Plot Double Double
    mass' =
        let s = printf "mass %6.4f" m
        in  hlinePlot s def m

layoutPdf :: (Ord r, Real r, QAlg r, Fractional r)
          => Int
          -> Mixed r
          -> Layout Double Double
layoutPdf n dq@(Mixed d ps) = layout_title .~ "ΔQ (pdf)"
                            $ layout_plots .~ [ toPlot $ lines n dq $ flip evalPW ps
                                              , plotBars bars
                                              , mean' dq
                                              ]
                            $ def
  where
    bars :: PlotBars Double Double
    bars = plot_bars_values .~ foldMapDisc (\r p -> [(toDouble r, [toDouble p])]) d
         $ plot_bars_spacing .~ BarsFixWidth 5
         $ plot_bars_item_styles .~ [(FillStyleSolid (opaque green), Nothing)]
         $ def

layoutMixed :: (Ord r, Real r, QAlg r, Fractional r)
         => Int
         -> Mixed r
         -> Grid (Renderable (LayoutPick Double Double Double))
layoutMixed n dq = layoutToGrid (layoutCdf n dq) ./. layoutToGrid (layoutPdf n dq)

toFileMixed :: (Ord r, Real r, QAlg r, Fractional r) => FilePath -> Mixed r -> IO ()
toFileMixed fp = void
            . renderableToFile def fp
            . fillBackground def
            . toRenderable . layoutMixed 1000

test :: IO ()
test = do
    let x    = scale (1 / 3) $ exactMixed 1 + exactMixed 3 + uniformMixed 7 10 :: Mixed Rational
        y    = scale (1 / 3) $ exactMixed 2 + uniformMixed 0 2 + uniformMixed 3 5 :: Mixed Rational
        xy   = x * y
        xxyy = x * x * y * y
        bxy  = before x y
        byx  = before y x
        axy  = after x y
        ayx  = after y x
        f    = ftf x y
        l    = ltf x y
        rxy  = residual x y
        ryx  = residual y x
    toFileMixed "x.png" x
    toFileMixed "y.png" y
    toFileMixed "convolve_x_y.png" xy
    toFileMixed "convolve_x_x_y_y.png" xxyy
    toFileMixed "before_x_y.png" bxy
    toFileMixed "before_y_x.png" byx
    toFileMixed "after_x_y.png" axy
    toFileMixed "after_y_x.png" ayx
    toFileMixed "ftf_x_y.png" f
    toFileMixed "ltf_x_y.png" l
    toFileMixed "residual_x_y.png" rxy
    toFileMixed "residual_y_x.png" ryx
