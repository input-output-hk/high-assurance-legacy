module Simulation.ThreadId
    ( ThreadId(..)
    ) where

newtype ThreadId = ThreadId Int deriving (Eq, Ord)

instance Show ThreadId where
    show (ThreadId n) = "#" ++ show n
