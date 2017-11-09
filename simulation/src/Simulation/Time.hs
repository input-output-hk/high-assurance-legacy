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
    show s = show (toMicroseconds s) ++ "μs"

instance Read Seconds where
    readsPrec n s = [(fromMicroseconds ms, t) | (ms, t) <- readsPrec n s]
