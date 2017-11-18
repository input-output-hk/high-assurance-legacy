module Simulation.Utils
    ( expectTimeout
    , logMessage
    , logMessageShow
    , observe
    , match
    , matches
    ) where

import Data.Maybe
import Data.Typeable
import Simulation.Thread.Class
import Simulation.Time

expectTimeout :: (MonadThread m, Typeable a) => ChannelT m a -> Seconds -> m (Maybe a)
expectTimeout c timeout = do
    c' <- newChannel
    e  <- fork $ expect c >>= \a -> send (Just a) c'
    t  <- fork $ delay timeout >> send Nothing c'
    ma <- expect c'
    kill e
    kill t
    return ma

logMessage :: MonadThread m => String -> m ()
logMessage = log' LogMessage

observe :: (Typeable a, MonadThread m) => a -> m ()
observe = log' Observation

log' :: MonadThread m => (Seconds -> ThreadIdT m -> a -> LogEntry (ThreadIdT m)) -> a -> m ()
log' f a = do
    s <- getTime
    tid <- getThreadId
    logEntryT $ f s tid a

logMessageShow :: (Show a, MonadThread m) => a -> m ()
logMessageShow = logMessage . show

match :: Typeable a => LogEntry threadId -> Maybe (Seconds, a)
match LogMessage{}        = Nothing
match (Observation s _ b) = (\a -> (s, a)) <$> cast b

matches :: Typeable a => [LogEntry threadId] -> [(Seconds, a)]
matches = mapMaybe match
