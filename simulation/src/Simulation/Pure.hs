{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Simulation.Pure
    ( simulateForT
    , simulateT
    , simulateFor
    , simulate
    , simulateForIO
    , simulateIO
    ) where

import           Control.Monad.State
import           Control.Monad.Trans.Free
import           Data.Foldable             (toList)
import           Data.Functor.Identity
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as M
import           Data.Typeable
import           Simulation.Channel
import           Simulation.Queue          (Queue)
import qualified Simulation.Queue          as Q
import           Simulation.Thread
import           Simulation.Thread.Class
import           Simulation.ThreadId
import           Simulation.Time
import           Simulation.TimeQueue      (TimeQueue)
import qualified Simulation.TimeQueue      as T
import           System.Random

data CHANNEL where
    CHANNEL :: Typeable a => Queue a -> CHANNEL

emptyCHANNEL :: forall a. Typeable a => Channel a -> CHANNEL
emptyCHANNEL _ = CHANNEL (Q.empty :: Queue a)

enqueueCHANNEL :: Typeable a => a -> CHANNEL -> CHANNEL
enqueueCHANNEL a (CHANNEL xs) =
    let Just ys = cast xs
    in  CHANNEL $ Q.enqueue a ys

dequeueCHANNEL :: Typeable a => Channel a -> CHANNEL -> Maybe (a, CHANNEL)
dequeueCHANNEL _ (CHANNEL q) = case Q.dequeue q of
    Nothing      -> Nothing
    Just (b, q') ->
        let Just a = cast b
        in  Just (a, CHANNEL q')

data ThreadState =
      Active
    | Expecting Int
    | Delayed Microseconds
    deriving Show

data Continuation m where
    Continuation :: Typeable a => ThreadId -> (a -> ThreadT m ()) -> Continuation m

callContinuation :: Typeable a => Continuation m -> a -> ThreadT m ()
callContinuation (Continuation _ k) a =
    let Just b = cast a
    in  k b

data SimState m = SimState
    { ssTime          :: Microseconds
    , ssNextThreadId  :: ThreadId
    , ssNextChannelId :: Int
    , ssThreads       :: Map ThreadId ThreadState
    , ssActive        :: Queue (ThreadId, ThreadT m ())
    , ssExpecting     :: Map Int (Continuation m)
    , ssDelayed       :: TimeQueue (ThreadId, ThreadT m ())
    , ssChannels      :: Map Int CHANNEL
    , ssLogs          :: Queue LogEntry
    , ssStdGen        :: StdGen
    }

initialState :: StdGen -> SimState m
initialState g = SimState
    { ssTime          = 0
    , ssNextThreadId  = ThreadId 1
    , ssNextChannelId = 0
    , ssThreads       = M.empty
    , ssActive        = Q.empty
    , ssExpecting     = M.empty
    , ssDelayed       = T.empty
    , ssChannels      = M.empty
    , ssLogs          = Q.empty
    , ssStdGen        = g
    }

type S m a = StateT (SimState m) m a

step :: forall m. Monad m => ThreadId -> ThreadT m () -> S m ()
step tid (ThreadT (FreeT t)) = do
    f <- lift t
    case f of
        Pure ()               -> return ()
        Free (GetThreadId k)  -> step tid $ ThreadT $ k tid
        Free (Fork t' k)      -> do
            tid'@(ThreadId n) <- gets ssNextThreadId
            modify $ \ss -> ss
                { ssNextThreadId = ThreadId $ n + 1
                , ssThreads      = M.insert tid' Active $ ssThreads ss
                , ssActive       = Q.enqueue (tid', t') $ ssActive ss
                }
            step tid $ ThreadT $ k tid'
        Free (Kill tid' t')   -> do
            ts <- gets ssThreads
            case M.lookup tid' ts of
                Nothing -> return ()
                Just st -> do
                    modify $ \ss -> ss {ssThreads = M.delete tid' ts}
                    modify $ \ss -> case st of
                        Active        -> ss {ssActive = Q.delete' ((== tid') . fst) $ ssActive ss}
                        Expecting cid -> ss {ssExpecting = M.delete cid $ ssExpecting ss}
                        Delayed s     -> ss {ssDelayed = T.delete' s ((== tid') . fst) $ ssDelayed ss}
            step tid $ ThreadT t'
        Free (NewChannel k)   -> do
            n <- gets ssNextChannelId
            let c = Channel n
            modify $ \ss -> ss
                { ssNextChannelId = n + 1
                , ssChannels      = M.insert n (emptyCHANNEL c) $ ssChannels ss
                }
            step tid $ ThreadT $ k c
        Free (Send a c t')    -> do
            e <- gets ssExpecting
            let Channel n = c
            case M.lookup n e of
                Nothing                      -> modify $ \ss -> ss {ssChannels = M.adjust (enqueueCHANNEL a) n $ ssChannels ss}
                Just k@(Continuation tid' _) -> modify $ \ss -> ss
                    { ssThreads   = M.insert tid' Active $ ssThreads ss
                    , ssActive    = Q.enqueue (tid', callContinuation k a) $ ssActive ss
                    , ssExpecting = M.delete n e
                    }
            step tid $ ThreadT t'
        Free (Expect c k)     -> do
            cs <- gets ssChannels
            let Channel n = c
            let h = cs M.! n
            case dequeueCHANNEL c h of
                Just (a, h') -> do
                    modify $ \ss -> ss {ssChannels = M.insert n h' $ ssChannels ss}
                    step tid $ ThreadT $ k a
                Nothing      -> modify $ \ss -> ss {ssExpecting = M.insert n (Continuation tid $ ThreadT . k) $ ssExpecting ss}
        Free (GetTime k)      -> gets ssTime >>= step tid . ThreadT . k
        Free (Delay d t')     -> do
            s <- gets ssTime
            let s' = s + d
            modify $ \ss -> ss
                { ssThreads = M.insert tid (Delayed s') $ ssThreads ss
                , ssDelayed = T.enqueue s' (tid, ThreadT t') $ ssDelayed ss
                }
        Free (Log e t')       -> do
            modify $ \ss -> ss {ssLogs = Q.enqueue e $ ssLogs ss}
            step tid $ ThreadT t'
        Free (WithStdGen r k) -> do
            g <- gets ssStdGen
            let (a, g') = r g
            modify $ \ss -> ss {ssStdGen = g'}
            step tid $ ThreadT $ k a

simulateForT :: forall m. Monad m => Maybe Microseconds -> StdGen -> ThreadT m () -> m ([LogEntry], StdGen)
simulateForT mms g = go (initialState g) $ ThreadId 0
  where
    go :: SimState m -> ThreadId -> ThreadT m () -> m ([LogEntry], StdGen)
    go s tid t = if ((>= ssTime s) <$> mms) /= Just False 
        then do
            s' <- execStateT (step tid t) s
            case (Q.dequeue $ ssActive s', T.dequeue $ ssDelayed s') of
                (Just ((tid', t'), q), _)            -> do
                    let s'' = s'
                            { ssThreads = M.delete tid' $ ssThreads s'
                            , ssActive  = q
                            }
                    go s'' tid' t'
                (Nothing, Just (ms, (tid', t'), tq)) -> do
                    let s'' = s'
                            { ssTime    = ms
                            , ssThreads = M.delete tid' $ ssThreads s'
                            , ssDelayed = tq
                            }
                    go s'' tid' t'
                (Nothing, Nothing)                   -> return $ result s'
        else return $ result s

    result :: SimState m -> ([LogEntry], StdGen)
    result s = (toList $ ssLogs s, ssStdGen s)

simulateT :: forall m. Monad m => StdGen -> ThreadT m () -> m ([LogEntry], StdGen)
simulateT = simulateForT Nothing

simulateFor :: Maybe Microseconds -> StdGen -> Thread () -> ([LogEntry], StdGen)
simulateFor mms g t = runIdentity $ simulateForT mms g t

simulate :: StdGen -> Thread () -> ([LogEntry], StdGen)
simulate = simulateFor Nothing

simulateForIO :: Maybe Microseconds -> Thread () -> IO ()
simulateForIO mms t = do
    g <- getStdGen
    let (logs, _) = simulateFor mms g t
    forM_ logs print

simulateIO :: Thread () -> IO ()
simulateIO = simulateForIO Nothing
