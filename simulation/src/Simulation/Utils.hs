module Simulation.Utils
    ( expectTimeout
    , logEntry
    , logEntryShow
    ) where

import Data.Typeable
import Simulation.Thread.Class
import Simulation.Time

expectTimeout :: (MonadThread m, Typeable a) => ChannelT m a -> Microseconds -> m (Maybe a)
expectTimeout c timeout = do
    c' <- newChannel
    e  <- fork $ expect c >>= \a -> send (Just a) c'
    t  <- fork $ delay timeout >> send Nothing c'
    ma <- expect c'
    kill e
    kill t
    return ma

logEntry :: ( Typeable a
            , MonadThread m
            , Show (ThreadIdT m)
            )
         => (a -> String)
         -> a
         -> m ()
logEntry sh a = do
    tid <- getThreadId
    ms  <- getTime
    logEntryT $ LogEntry ms tid a sh

logEntryShow :: ( Show a
                , Typeable a
                , MonadThread m
                , Show (ThreadIdT m)
                )
             => a
             -> m ()
logEntryShow = logEntry show
