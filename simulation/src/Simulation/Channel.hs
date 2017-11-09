module Simulation.Channel
    ( Channel(..)
    , Channels
    , empty
    , enqueue
    , dequeue
    ) where

import           Data.Maybe       (fromMaybe)
import           Data.Typeable    (Typeable)
import           Simulation.HMap  (IsKey, HMap)
import qualified Simulation.HMap  as H
import           Simulation.Queue (Queue)
import qualified Simulation.Queue as Q

newtype Channel a = Channel Int

instance Show (Channel a) where
    show (Channel n) = "#" ++ show n

instance IsKey Channel where
    type Key Channel = Int
    key (Channel n) = n

type Channels = HMap Channel Queue

empty :: Channels
empty = H.empty

enqueue :: Typeable a => Channel a -> a -> Channels -> Channels
enqueue ca a cs = H.insert
    ca
    (Q.enqueue a $ fromMaybe Q.empty $ H.lookup ca cs)
    cs

dequeue :: Typeable a => Channel a -> Channels -> Maybe (a, Channels)
dequeue ca cs = case H.lookup ca cs of
    Nothing -> Nothing
    Just q  ->
        let Just (a, q') = Q.dequeue q
        in  Just (a, if Q.null q' then H.delete ca cs
                                  else H.insert ca q' cs)
