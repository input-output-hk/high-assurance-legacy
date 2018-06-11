module Simulation.Time
    ( Seconds
    , toMicroseconds
    , fromMicroseconds
    ) where

newtype Seconds = Seconds Rational deriving (Eq, Ord, Num, Real, Fractional, RealFrac)

toMicroseconds :: Seconds -> Integer
toMicroseconds = round . (* 1000000) . toRational

fromMicroseconds :: Integer -> Seconds
fromMicroseconds = (/ 1000000) . fromIntegral

instance Show Seconds where
    show s = show (fromRational $ toRational s :: Double) ++ "s"

instance Read Seconds where
    readsPrec n s = [(fromRational $ toRational d, t) | (d :: Double, t) <- readsPrec n s]
