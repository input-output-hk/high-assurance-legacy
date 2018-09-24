{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Graph
    ( Node
    , Graph
    , GraphBuilder
    , addNode
    , addEdge
    , buildGraph
    , networkP
    , graphIO
    ) where

import           Control.Monad
import           Control.Monad.State
import           Data.DeltaQ
import           Data.DeltaQ.PList
import           Data.Maybe          (mapMaybe)
import qualified Data.Polynomial     as P
import           Pipes
import           Process
import           Text.Printf         (printf)

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
    inp :>: PrCont (\s -> let n = read s in f n ns)
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
    go m ns = Nu $ PrCont (\inp -> go (m - 1) ((m, inp) : ns))

stepState :: (Mixed, Mixed, Message) -> [Int] -> PState Mixed [Int]
stepState (_, dqAbs, Message _ msg) ns =
    case filter (/= read msg) ns of
        []  -> Success dqAbs
        ns' -> Undecided ns'

initState :: Int -> [Int]
initState n = [1..n]

pipeGraph :: Monad m
          => Mixed
          -> Graph
          -> Producer (Prob Rational, Maybe Mixed) m ()
pipeGraph dq g@(n, _) = pipePList'
    stepState
    [1..n]
    (toPList' $ toPList $ toTrace $ networkP dq g)

consumer :: Monad m
         => (Rational -> Rational -> Mixed -> m ())
         -> (Mixed -> m ())
         -> Consumer (Prob Rational, Maybe Mixed) m ()
consumer report process = go 0 0 0
  where
    go !s !f !d = do
        (p, m) <- await
        let p' = getProb p
            (s', f', d') = case m of
                Nothing        -> (s, f + p', d)
                Just (Mixed e) -> (s + p', f, d + P.scale p' e)
        lift $ report s' f' (Mixed d')
        when (s' + f' == 1) $ lift $ process $ Mixed d'
        go s' f' d'

graphIO :: Mixed -> Graph -> (Mixed -> IO ()) -> IO ()
graphIO dq g process = runEffect $ pipeGraph dq g >-> consumer report process'
  where
    report :: Rational -> Rational -> Mixed -> IO ()
    report s f _ = do
        let s' = fromRational s :: Double
            f' = fromRational f :: Double
        printf "%6.4f %6.4f %6.4f\n" (s' + f') s' f'

    process' :: Mixed -> IO ()
    process' res = do
        let massd = fromRational $ getProb $ mass res :: Double
        printf "mass: %6.4f\n" massd
        process res
