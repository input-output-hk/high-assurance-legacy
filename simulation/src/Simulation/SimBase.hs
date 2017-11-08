{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Simulation.SimBase
    ( LogEntry(..)
    , MonadSim(..)
    , MonadThreadPlus
    , logEntry
    , SimBaseT
    , getLogsT
    , getLogs
    , getLogsIO
    ) where

import Control.Monad.State
import Data.Functor.Identity
import Data.Typeable
import Simulation.Pure
import Simulation.Thread.Class
import Simulation.Time
import System.Random
import Text.Printf

data LogEntry where
    LogEntry :: ( Show threadId
                , Typeable a
                , Show a
                )
             => Microseconds -> threadId -> a -> LogEntry

instance Show LogEntry where
    show (LogEntry ms tid a) = printf "%12s: %4s: %s" (show ms) (show tid) (show a)

class Monad m => MonadSim m where
    logEntryM  :: LogEntry -> m ()
    withStdGen :: (StdGen -> (a, StdGen)) -> m a

type MonadThreadPlus m = (MonadThread m, MonadSim m, Show (ThreadId m))

instance MonadSim m => MonadSim (M m) where
    logEntryM  = lift . logEntryM
    withStdGen = lift . withStdGen

logEntry :: ( Show a
            , Typeable a
            , MonadThreadPlus m
            , Show (ThreadId m)
            )
         => a -> m ()
logEntry a = do
    tid <- getThreadId
    ms  <- getTime
    logEntryM $ LogEntry ms tid a

instance MonadSim IO where
    logEntryM  = print
    withStdGen = getStdRandom

data SimBaseState = SimBaseState
    { bsLogs   :: [LogEntry]
    , bsStdGen :: StdGen
    }

initialSimBaseState :: StdGen -> SimBaseState
initialSimBaseState g = SimBaseState
    { bsLogs   = []
    , bsStdGen = g
    }

newtype SimBaseT m a = SimBaseT {runSimBaseT :: StateT SimBaseState m a}
    deriving (Functor, Applicative, Monad, MonadState SimBaseState, MonadTrans)

instance Monad m => MonadSim (SimBaseT m) where
    logEntryM e   = modify $ \bs -> bs {bsLogs = e : bsLogs bs}
    withStdGen f = do
        g <- gets bsStdGen
        let (a, g') = f g
        modify $ \bs -> bs {bsStdGen = g'}
        return a

type SimBase = SimBaseT Identity

getLogsT :: Monad m => Maybe Microseconds -> StdGen -> M (SimBaseT m) () -> m ([LogEntry], StdGen)
getLogsT mms g t = do
    bs <- execStateT (runSimBaseT $ simulateFor mms t) $ initialSimBaseState g
    return (reverse $ bsLogs bs, bsStdGen bs)

getLogs :: Maybe Microseconds -> StdGen -> M SimBase () -> ([LogEntry], StdGen)
getLogs mms g = runIdentity . getLogsT mms g

getLogsIO :: Maybe Microseconds -> M SimBase () -> IO ()
getLogsIO mms t = do
    g <- getStdGen
    let (logs, _) = getLogs mms g t
    forM_ logs print
