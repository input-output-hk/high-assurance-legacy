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
    , measureM
    , probMDQ
    , weighted
    ) where

import           Control.Monad
import           Control.Monad.Operational
import           Control.Monad.State
import           Data.DeltaQ
import           Data.DeltaQ.PList
import           Data.List.NonEmpty        (NonEmpty (..))
import qualified Data.List.NonEmpty        as NE
import           Data.Maybe                (mapMaybe)
import           Process

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

measureM :: forall p t dq m. (DeltaQ p t dq, MonadProb p m)
         => Graph
         -> dq
         -> m dq
measureM g@(n, _) dq = go [1..n] (exact now) $ toTrace (networkP dq g)
  where
    go :: [Int] -> dq -> MList m (dq, Message) -> m dq
    go [] clock _         = return clock
    go ns clock (MList l) = do
        m <- l
        case m of
            Nothing                -> return never
            Just ((dq', msg), l') -> do
                let node   = read (msgPayload msg)
                    clock' = clock <> dq'
                if node `elem` ns
                    then go (filter (/= node) ns) clock' l'
                    else go ns                    clock' l'

probMDQ :: forall p t dq. DeltaQ p t dq => ProbM p dq -> dq
probMDQ (ProbT prog) = go $ view prog
  where
    go :: ProgramView (ProbI p) dq -> dq
    go (Return dq)            = dq
    go (Coin p a b :>>= cont) =
        let !dqa = goCont cont a
            !dqb = goCont cont b
            !dq' = mix p dqa dqb
        in  dq'
    go (Elements xs :>>= cont) = weighted $ goCont cont <$> xs

    goCont :: (a -> Program (ProbI p) dq) -> a -> dq
    goCont cont = probMDQ . ProbT . cont

weighted :: DeltaQ p t dq => NonEmpty dq -> dq
weighted xs = go' (NE.length xs) xs
  where
    go' _  (dq :| [])       = dq
    go' !n (dq :| (y : ys)) =
        let !p = prob $ recip $ fromIntegral n
        in  mix p dq $ go' (n - 1) (y :| ys)
