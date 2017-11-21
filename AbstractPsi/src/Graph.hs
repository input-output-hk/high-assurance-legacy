module Graph
    ( previewGraph
    , previewGraph'
    , toPng
    , toPng'
    ) where

import           Control.Monad                     (unless, void, forM_)
import           Control.Monad.State               (State)
import qualified Control.Monad.State               as S
import           Data.Bifunctor                    (second)
import           Data.Functor.Const                (Const (..))
import           Data.Graph.Inductive.PatriciaTree (Gr)
import           Data.Graph.Inductive.Graph        (Node)
import qualified Data.Graph.Inductive.Graph        as G
import qualified Data.GraphViz                     as GV
import           Data.Map.Strict                   (Map)
import qualified Data.Map.Strict                   as M
import           Initial
import           Psi

type P v = IPsi (Const Int) v

type G = Gr String (Maybe Int)

data S v = S
    { sActive   :: [(P v, Maybe Node)]
    , sBlocked  :: Map Int ([(P v, Node)], [(P v, Node)])
    , sNextChan :: !Int
    , sGraph    :: G
    }           

initS :: P v -> S v
initS p = S
    { sActive   = [(p, Nothing)]
    , sBlocked  = M.empty
    , sNextChan = 1
    , sGraph    = G.empty
    }

step :: State (S v) Bool
step = do
    ps <- S.gets sActive
    case ps of
        []                      -> do
            m <- S.gets sBlocked
            if M.null m
                then return True
                else do
                    forM_ (M.toList m) $ \(c, (outs, ins)) -> case (outs, ins) of
                        ([], _) -> return ()
                        (_, []) -> return ()
                        _       -> do
                            forM_ (outs ++ ins) $ \(p, n) ->
                                S.modify $ \s -> s {sActive = (p, Just n) : sActive s}
                            forM_ outs $ \(_, n) ->
                                forM_ ins $ \(_, n') ->
                                   S.modify $ \s -> s {sGraph = G.insEdge (n, n', Just c) $ sGraph s} 
                    S.modify $ \s -> s {sBlocked = M.empty}
                    return False
        ((Done, mn) : ps')      -> do
            _ <- addNode "done" mn
            S.modify $ \s -> s {sActive = ps'}
            return False
        ((Fork p q, mn) : ps')  -> do
            n <- addNode "fork" mn
            S.modify $ \s -> s {sActive = (p, Just n) : (q, Just n) : ps'}
            return False
        ((Nu k, mn) : ps')      -> do
            i <- S.gets sNextChan
            let c = Const i
            n <- addNode ("ν(" ++ show i ++ ")") mn
            S.modify $ \s -> s 
                { sActive   = (k c, Just n) : ps'
                , sNextChan = i + 1
                }
            return False
        ((Out c _ p, mn) : ps') -> do
            let i = getConst c
            n <- addNode ("out(" ++ show i ++ ")") mn
            m <- S.gets sBlocked
            let (outs, ins) = M.findWithDefault ([], []) i m
                m' = M.insert i ((p, n) : outs, ins) m
            S.modify $ \s -> s
                { sActive  = ps'
                , sBlocked = m'
                }
            return False
        ((Inp c k, mn) : ps')   -> do
            let i = getConst c
            n <- addNode ("inp(" ++ show i ++ ")") mn
            m <- S.gets sBlocked
            let (outs, ins) = M.findWithDefault ([], []) i m
                m' = M.insert i (outs, (k undefined, n) : ins) m
            S.modify $ \s -> s
                { sActive  = ps'
                , sBlocked = m'
                }
            return False

steps :: State (S v) ()
steps = do
    b <- step
    unless b steps

toGraph :: IPsi (Const Int) v -> G
toGraph = sGraph . S.execState steps . initS

previewGraph :: IPsi (Const Int) v -> IO ()
previewGraph = GV.preview . second (maybe "" show) . toGraph

previewGraph' :: (forall p. Psi p => p) -> IO ()
previewGraph' p = previewGraph $ toInitial p

toPng :: IPsi (Const Int) v -> FilePath -> IO ()
toPng p file =
    let params = GV.nonClusteredParams
            { GV.fmtNode = \(_, l) -> [GV.toLabel l]
            , GV.fmtEdge = \(_, _, l) -> [GV.toLabel l]
            }
        dg = GV.graphToDot params $ second (maybe "" show) $ toGraph p
    in  void $ GV.runGraphviz dg GV.Png file

toPng' :: (forall p. Psi p => p) -> FilePath -> IO ()
toPng' p = toPng (toInitial p)

addNode :: String -> Maybe Node -> State (S v) Node
addNode l mn = do
    g <- S.gets sGraph
    let [n] = G.newNodes 1 g
        g'  = G.insNode (n, l) g
        g'' = case mn of
            Nothing -> g'
            Just n' -> G.insEdge (n', n, Nothing) g'
    S.modify $ \s -> s {sGraph = g''}
    return n
