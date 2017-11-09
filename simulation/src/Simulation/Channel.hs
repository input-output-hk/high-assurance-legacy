module Simulation.Channel
    ( Channel(..)
    ) where

newtype Channel a = Channel Int

instance Show (Channel a) where
    show (Channel n) = "#" ++ show n
