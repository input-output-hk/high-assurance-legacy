module Simulation.Utils
    ( expectTimeout
    ) where

import Data.Typeable
import Simulation.Thread.Class
import Simulation.Time

expectTimeout :: (MonadThread m, Typeable a) => Channel m a -> Microseconds -> m (Maybe a, Microseconds)
expectTimeout c timeout = do
    c'    <- newChannel
    start <- getTime
    e     <- fork $ do
        a <- expect c
        send (Just a) c'
    t     <- fork $ do
        delay timeout
        send Nothing c'
    ma    <- expect c'
    end   <- getTime
    kill e
    kill t
    return (ma, end - start)
