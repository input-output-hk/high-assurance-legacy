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
import           Simulation.Channel        (Channel(..), Channels)
import qualified Simulation.Channel        as C
import           Simulation.HMap           (HMap)
import qualified Simulation.HMap           as H
import           Simulation.Queue          (Queue)
import qualified Simulation.Queue          as Q
import           Simulation.Thread
import           Simulation.Thread.Class
import           Simulation.ThreadId
import           Simulation.Time
import           Simulation.TimeQueue      (TimeQueue)
import qualified Simulation.TimeQueue      as T
import           System.Random

data ThreadState where
    Active    :: ThreadState
    Expecting :: !(Channel a) -> ThreadState
    Delayed   :: !Seconds -> ThreadState

data Continuation m a = Continuation !ThreadId !(a -> ThreadT m ())

callContinuation :: Continuation m a -> a -> ThreadT m ()
callContinuation (Continuation _ k) = k

data SimState m = SimState
    { ssTime          :: Seconds
    , ssNextThreadId  :: ThreadId
    , ssNextChannelId :: Int
    , ssThreads       :: Map ThreadId ThreadState
    , ssActive        :: Queue (ThreadId, ThreadT m ())
    , ssExpecting     :: HMap Channel (Continuation m)
    , ssDelayed       :: TimeQueue (ThreadId, ThreadT m ())
    , ssChannels      :: Channels
    , ssLogs          :: Queue (LogEntry ThreadId)
    , ssStdGen        :: StdGen
    }

initialState :: StdGen -> SimState m
initialState g = SimState
    { ssTime          = 0
    , ssNextThreadId  = ThreadId 1
    , ssNextChannelId = 0
    , ssThreads       = M.empty
    , ssActive        = Q.empty
    , ssExpecting     = H.empty
    , ssDelayed       = T.empty
    , ssChannels      = C.empty
    , ssLogs          = Q.empty
    , ssStdGen        = g
    }

type S m a = StateT (SimState m) m a

step :: forall m. (Monad m, Typeable m) => ThreadId -> ThreadT m () -> S m ()
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
                        Active      -> ss {ssActive = Q.delete' ((== tid') . fst) $ ssActive ss}
                        Expecting c -> ss {ssExpecting = H.delete c $ ssExpecting ss}
                        Delayed s   -> ss {ssDelayed = T.delete' s ((== tid') . fst) $ ssDelayed ss}
            step tid $ ThreadT t'
        Free (NewChannel k)   -> do
            n <- gets ssNextChannelId
            modify $ \ss -> ss {ssNextChannelId = n + 1}
            step tid $ ThreadT $ k $ Channel n
        Free (Send a c t')    -> do
            e <- gets ssExpecting
            case H.lookup c e of
                Nothing                      -> modify $ \ss -> ss {ssChannels = C.enqueue c a $ ssChannels ss}
                Just k@(Continuation tid' _) -> modify $ \ss -> ss
                    { ssThreads   = M.insert tid' Active $ ssThreads ss
                    , ssActive    = Q.enqueue (tid', callContinuation k a) $ ssActive ss
                    , ssExpecting = H.delete c e
                    }
            step tid $ ThreadT t'
        Free (Expect c k)     -> do
            cs <- gets ssChannels
            case C.dequeue c cs of
                Nothing       -> modify $ \ss -> ss {ssExpecting = H.insert c (Continuation tid $ ThreadT . k) $ ssExpecting ss}
                Just (a, cs') -> do
                    modify $ \ss -> ss {ssChannels = cs'}
                    step tid $ ThreadT $ k a
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

simulateForT :: forall m. (Monad m, Typeable m) => Maybe Seconds -> StdGen -> ThreadT m () -> m ([LogEntry ThreadId], StdGen)
simulateForT mms g = go (initialState g) $ ThreadId 0
  where
    go :: SimState m -> ThreadId -> ThreadT m () -> m ([LogEntry ThreadId], StdGen)
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

    result :: SimState m -> ([LogEntry ThreadId], StdGen)
    result s = (toList $ ssLogs s, ssStdGen s)

simulateT :: forall m. (Monad m, Typeable m) => StdGen -> ThreadT m () -> m ([LogEntry ThreadId], StdGen)
simulateT = simulateForT Nothing

simulateFor :: Maybe Seconds -> StdGen -> Thread () -> ([LogEntry ThreadId], StdGen)
simulateFor mms g t = runIdentity $ simulateForT mms g t

simulate :: StdGen -> Thread () -> ([LogEntry ThreadId], StdGen)
simulate = simulateFor Nothing

simulateForIO :: Maybe Seconds -> Thread () -> IO ()
simulateForIO mms t = do
    g <- getStdGen
    let (logs, _) = simulateFor mms g t
    forM_ logs print

simulateIO :: Thread () -> IO ()
simulateIO = simulateForIO Nothing
