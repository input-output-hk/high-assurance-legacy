module Simulation.Time
    ( Microseconds
    ) where

newtype Microseconds = Microseconds Int deriving (Eq, Ord, Num, Enum, Integral, Real)

instance Show Microseconds where
    show (Microseconds ms) = show ms ++ "μs"

instance Read Microseconds where
    readsPrec n s = [(Microseconds ms, t) | (ms, t) <- readsPrec n s]
