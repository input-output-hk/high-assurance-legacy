{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Simulation.SimBase
    ( LogEntry(..)
    , MonadSim(..)
    , MonadThreadPlus
    , logEntry
    , withStdGen
    , SimBaseT
    , getLogsT
    , getLogs
    ) where

import Control.Monad.State
import Data.Functor.Identity
import Data.Typeable
import Simulation.Pure
import Simulation.Thread.Class
import Simulation.Time
import System.Random

data LogEntry where
    LogEntry :: ( Show threadId
                , Typeable a
                , Show a
                )
             => Microseconds -> threadId -> a -> LogEntry

instance Show LogEntry where
    show (LogEntry ms tid a) = show ms ++ ": " ++ show tid ++ ": " ++ show a

class Monad m => MonadSim m where
    logEntryM   :: LogEntry -> m ()
    withStdGenM :: (StdGen -> (a, StdGen)) -> m a

type MonadThreadPlus m = (MonadThread m, MonadSim m, Show (ThreadId m))

instance MonadSim m => MonadSim (M m) where
    logEntryM   = lift . logEntryM
    withStdGenM = lift . withStdGenM

logEntry :: ( Show a
            , Typeable a
            , MonadSim m
            , MonadThread m
            , Show (ThreadId m)
            ) 
         => a -> m ()
logEntry a = do
    tid <- getThreadId
    ms  <- getTime
    logEntryM $ LogEntry ms tid a

withStdGen :: MonadSim m => (StdGen -> (a, StdGen)) -> M m a
withStdGen f = lift $ withStdGenM f

instance MonadSim IO where
    logEntryM   = print
    withStdGenM = getStdRandom

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
    withStdGenM f = do
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
