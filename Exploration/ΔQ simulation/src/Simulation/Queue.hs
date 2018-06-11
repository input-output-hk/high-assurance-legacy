module Simulation.Queue
    ( Queue
    , empty
    , null
    , enqueue
    , dequeue
    , toList
    , fromList
    , delete'
    , delete
    ) where

import           Data.Foldable
import           Data.Traversable
import           Prelude          hiding (null)

data Queue a = Queue [a] [a] deriving (Show)

empty :: Queue a
empty = Queue [] []

enqueue :: a -> Queue a -> Queue a
enqueue a (Queue xs ys) = Queue xs (a : ys)

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue (Queue [] [])        = Nothing
dequeue (Queue (x : xs) ys)  = Just (x, Queue xs ys)
dequeue (Queue [] ys)        = dequeue $ Queue (reverse ys) []

instance Functor Queue where
    fmap = fmapDefault

instance Foldable Queue where
    foldMap = foldMapDefault

instance Traversable Queue where
    traverse f (Queue xs ys) = 
            (\us vs -> Queue us $ reverse vs) 
        <$> traverse f xs 
        <*> traverse f (reverse ys)

fromList :: [a] -> Queue a
fromList = foldl' (flip enqueue) empty

delete' :: (a -> Bool) -> Queue a -> Queue a
delete' p = fromList . filter (not . p) . toList

delete :: Eq a => a -> Queue a -> Queue a
delete a = delete' (== a)

