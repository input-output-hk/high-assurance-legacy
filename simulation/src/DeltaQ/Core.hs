module DeltaQ.Core
    ( DeltaQ (runDeltaQ)
    , dirac
    , perfection
    , bottom
    , mix
    , uniformFromZero
    , between
    ) where

import Data.Monoid ((<>))
import Simulation.Time
import System.Random

newtype DeltaQ = DeltaQ {runDeltaQ :: StdGen -> (Maybe Seconds, StdGen)}

dirac :: Maybe Seconds -> DeltaQ
dirac (Just s)
    | s < 0 = error "seconds must not be negative"
dirac s = DeltaQ $ \g -> (s, g)

perfection, bottom :: DeltaQ
perfection = dirac $ Just 0
bottom     = dirac Nothing

instance Monoid DeltaQ where
    mempty                      = perfection
    DeltaQ a `mappend` DeltaQ b = DeltaQ $ \g ->
        let  (mda, g')   = a g
             (mdb, g'')  = b g'
             md          = (+) <$> mda <*> mdb
        in   (md, g'')

mix :: (DeltaQ, Rational) -> (DeltaQ, Rational) -> DeltaQ
(DeltaQ a, wa) `mix` (DeltaQ b, wb)
    | wa < 0 || wb < 0 || wa + wb == 0  = error "weights must not be negative, and one must be positive"
    | otherwise                         = DeltaQ $ \g ->
        let  pa       = fromRational $ wa / (wa + wb)
             (r, g')  = randomR (0 :: Double, 1) g
        in   (if r <= pa then a else b) g'

uniformFromZero :: Seconds -> DeltaQ
uniformFromZero s
    |  s < 0      = error "seconds must not be negative"
    |  s == 0     = perfection
    |  otherwise  = DeltaQ $ \g ->
        let (d, g')  = randomR (0 :: Double, fromRational $ toRational s) g
            md       = Just $ min s $ max 0 $ fromRational $ toRational d
        in  (md, g')

between :: (Seconds, Seconds) -> DeltaQ
between (a, b) = dirac (Just a) <> uniformFromZero (b - a)
