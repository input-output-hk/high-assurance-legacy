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
import           Data.IntMap.Strict  (IntMap)
import qualified Data.IntMap.Strict  as IM
import           Data.Maybe          (mapMaybe)
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

ticker :: forall p t dq. (Num t, DeltaQ p t dq) => Chan -> Process dq
ticker lg = Nu $ PrCont $ \ch ->
        ch :<: (dq1, ".")
    :|: listener ch
  where
    listener :: Chan -> Process dq
    listener ch = ch :>: (PrCont $ const $
            lg  :<: (dq0, "TICK")
        :|: ch :<: (dq1, ".")
        :|: listener ch)

    dq0, dq1 :: dq
    dq0 = exact now
    dq1 = exact (Finite 1)

networkP :: forall p t dq. (DeltaQ p t dq, Num t)
         => dq
         -> Graph
         -> Chan
         -> Process dq
networkP dq g@(n, _) lg = go n []
  where
    go :: Node -> [(Node, Chan)] -> Process dq
    go 0 ns = nodesP dq g ns lg :|: ticker lg
    go m ns = Nu $ PrCont (\inp -> go (m - 1) ((m, inp) : ns))

stepState :: Int
          -> (Mixed, Message)
          -> ([Int], Int)
          -> PState Int ([Int], Int)
stepState timeout (_, Message _ "TICK") (ns, t)
    | t == timeout - 1 = Failure
    | otherwise        = Undecided (ns, t + 1)
stepState _       (_, Message _ msg)    (ns, t) =
    case filter (/= read msg) ns of
        []  -> Success $ t + 1
        ns' -> Undecided (ns', t)

pipeGraph :: Monad m
          => Mixed
          -> Int
          -> Graph
          -> Producer (Prob Rational, Maybe Int) m ()
pipeGraph dq timeout g@(n, _) = pipePList'
    (stepState timeout)
    ([1..n], 0)
    (toPList' $ toPList $ toTrace $ networkP dq g)

consumer :: forall m. Monad m
         => (Rational -> Rational -> Maybe Int -> IntMap Rational -> m ())
         -> (IntMap Rational -> m ())
         -> Consumer (Prob Rational, Maybe Int) m ()
consumer report process = go 0 0 IM.empty
  where
    go !s !f !d = do
        (p, m) <- await
        let p' = getProb p
            (s', f', d') = case m of
                Nothing -> (s, f + p', d)
                Just t  -> (s + p', f, IM.insertWith (+) t p' d)
        lift $ report s' f' m d'
        when (s' + f' == 1) $ lift $ process d'
        go s' f' d'

graphIO :: Mixed -> Int -> Graph -> (IntMap Rational -> IO ()) -> IO ()
graphIO dq timeout g process =
    runEffect $ pipeGraph dq timeout g >-> consumer report process'
  where
    report :: Rational -> Rational -> Maybe Int -> IntMap Rational -> IO ()
    report s f m _ = do
        let s' = fromRational s :: Double
            f' = fromRational f :: Double
        printf "%6.4f %6.4f %6.4f %s\n" (s' + f') s' f' (show m)

    process' :: IntMap Rational -> IO ()
    process' res = do
        forM_ (IM.toList res) $ \(t, p) ->
            printf "%3d: %6.4f\n" t (fromRational p :: Double)
        process res
