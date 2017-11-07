module Simulation.Thread.Class
    ( MonadThread(..)
    ) where

import qualified Control.Concurrent           as C
import qualified Control.Concurrent.STM       as STM
import           Control.Monad.Trans.Identity
import           Data.Time.Clock.POSIX        (getPOSIXTime)
import           Data.Typeable                (Typeable)
import           Simulation.Time

class Monad m => MonadThread m where

    type ThreadId m :: *
    type Channel m :: * -> *

    getThreadId :: m (ThreadId m)
    fork        :: m () -> m (ThreadId m)
    kill        :: ThreadId m -> m ()
    newChannel  :: Typeable a => m (Channel m a)
    send        :: Typeable a => a -> Channel m a -> m ()
    expect      :: Typeable a => Channel m a -> m a
    getTime     :: m Microseconds
    delay       :: Microseconds -> m ()

instance MonadThread IO where

    type ThreadId IO = C.ThreadId
    type Channel IO = STM.TChan

    getThreadId = C.myThreadId
    fork        = C.forkIO
    kill        = C.killThread
    newChannel  = STM.newTChanIO
    send a c    = STM.atomically $ STM.writeTChan c a
    expect      = STM.atomically . STM.readTChan
    getTime     = round . (* 1000000) <$> getPOSIXTime
    delay       = C.threadDelay . fromIntegral

instance MonadThread m => MonadThread (IdentityT m) where

    type ThreadId (IdentityT m) = ThreadId m
    type Channel (IdentityT m) = Channel m

    getThreadId = IdentityT getThreadId
    fork        = IdentityT . fork . runIdentityT
    kill        = IdentityT . kill
    newChannel  = IdentityT newChannel
    send a c    = IdentityT $ send a c
    expect      = IdentityT . expect
    getTime     = IdentityT getTime
    delay       = IdentityT . delay
