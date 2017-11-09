module Simulation.TimeQueue
    ( TimeQueue
    , empty
    , null
    , enqueue
    , dequeue
    , fromList
    , toList
    , delete'
    ) where

import           Data.List        (foldl')
import           Data.Map.Strict  (Map)
import qualified Data.Map.Strict  as M
import           Prelude          hiding (null)
import           Simulation.Queue (Queue)
import qualified Simulation.Queue as Q
import           Simulation.Time

newtype TimeQueue a = TimeQueue (Map Seconds (Queue a))

empty :: TimeQueue a
empty = TimeQueue M.empty

null :: TimeQueue a -> Bool
null (TimeQueue m) = M.null m

enqueue :: forall a. Seconds -> a -> TimeQueue a -> TimeQueue a
enqueue s a (TimeQueue m) = TimeQueue $ M.alter f s m
  where
    f :: Maybe (Queue a) -> Maybe (Queue a)
    f Nothing   = Just $ Q.enqueue a Q.empty
    f (Just q)  = Just $ Q.enqueue a q

dequeue :: TimeQueue a -> Maybe (Seconds, a, TimeQueue a)
dequeue (TimeQueue m) = case M.minViewWithKey m of
    Nothing            -> Nothing
    Just ((s, q), m')  ->
        let  Just (a, q')  = Q.dequeue q
             m''           = if Q.null q' then m' else M.insert s q' m'
        in   Just (s, a, TimeQueue m'')

fromList :: [(Seconds, a)] -> TimeQueue a
fromList = foldl' f empty
  where
    f :: TimeQueue a -> (Seconds, a) -> TimeQueue a
    f t (s, a) = enqueue s a t

toList :: TimeQueue a -> [(Seconds, a)]
toList t = case dequeue t of
    Nothing         -> []
    Just (s, a, t') -> (s, a) : toList t'

delete' :: forall a. Seconds -> (a -> Bool) -> TimeQueue a -> TimeQueue a
delete' s p (TimeQueue m) = TimeQueue $ M.alter f s m
  where
    f :: Maybe (Queue a) -> Maybe (Queue a)
    f Nothing  = Nothing
    f (Just q) =
        let q' = Q.delete' p q
        in  if Q.null q' then Nothing else Just q'
