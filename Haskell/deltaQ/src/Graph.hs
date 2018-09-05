{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Graph
    ( Node
    , Graph
    , GraphBuilder
    , addNode
    , addEdge
    , buildGraph
    , measure
    , DQ
    , M
    ) where

import Control.Monad
import Control.Monad.State
import Data.DeltaQ
import Data.Maybe          (mapMaybe)
import Process

type Node = Int
type Graph = (Int, [(Node, Node)])

newtype GraphBuilder a = GraphBuilder (State Graph a)
    deriving (Functor, Applicative, Monad)

emptyGraph :: Graph
emptyGraph = (0, [])

addNode :: GraphBuilder Node
addNode = do
    (n, es) <- GraphBuilder get
    let n' = n + 1
    GraphBuilder $ put (n', es)
    return n'

addEdge :: Node -> Node -> GraphBuilder ()
addEdge x y
    | x == y           = return ()
    | x <= 0 || y <= 0 = error "illegal node"
    | y < x            = addEdge y x
    | otherwise        = do
        (n, es) <- GraphBuilder get
        if y > n
            then error "illegal node"
            else do
                let e = (x, y)
                when (e `notElem` es) $
                    GraphBuilder $ put (n, e : es)

buildGraph :: GraphBuilder a -> Graph
buildGraph (GraphBuilder m) = execState m emptyGraph

neighbors :: Node -> Graph -> [Node]
neighbors n (_, es) = mapMaybe f es
  where
    f (a, b)
        | a == n    = Just b
        | b == n    = Just a
        | otherwise = Nothing

nodeP :: forall p t dq. DeltaQ p t dq
      => dq
      -> Node
      -> [(Node, Chan)]
      -> Chan
      -> Chan
      -> Process dq
nodeP dq node ns inp lg =
    inp :>: \s -> let n = read s in f n ns
  where
    f :: Node -> [(Node, Chan)] -> Process dq
    f _ []             = lg :<: (exact now, show node)
    f n ((m, ch) : xs)
        | m == n       = f n xs
        | otherwise    = (ch :<: (dq, show node)) :|: f n xs

nodesP :: forall p t dq. DeltaQ p t dq
      => dq
      -> Graph
      -> [(Node, Chan)]
      -> Chan
      -> Process dq
nodesP dq g@(n, _) ns lg = go n
  where
    go :: Node -> Process dq
    go 0 = findChan 1 :<: (exact now, "0")
    go m = do
        let inp = findChan m
            xs  = neighbors m g
            ns' = filter (\(k, _) -> k /= m && k `elem` xs) ns
        nodeP dq m ns' inp lg :|: go (m - 1)

    findChan :: Node -> Chan
    findChan m = head $ map snd $ filter (\(k, _) -> k == m) ns

networkP :: forall p t dq. DeltaQ p t dq
         => dq
         -> Graph
         -> Chan
         -> Process dq
networkP dq g@(n, _) lg = go n []
  where
    go :: Node -> [(Node, Chan)] -> Process dq
    go 0 ns = nodesP dq g ns lg
    go m ns = Nu $ \inp -> go (m - 1) ((m, inp) : ns)

type DQ = DDQ Double IntP
type M = DeltaQM Double IntP DQ

measure :: Graph -> DQ -> DQ
measure g@(n, _) dq = timing $ f q
  where
    q :: QueueDQ M Message
    q = toQueue $ networkP dq g

    f :: QueueDQ M Message -> M ()
    f = go [1..n]
      where
        go :: [Node] -> QueueDQ M Message -> M ()
        go [] _ = return ()
        go ns q' = do
            m <- dequeueDQ q'
            case m of
                Nothing        -> delay never
                Just (msg, q'') -> do
                    let i   = read $ msgPayload msg
                        ns' = filter (/= i) ns
                    go ns' q''
