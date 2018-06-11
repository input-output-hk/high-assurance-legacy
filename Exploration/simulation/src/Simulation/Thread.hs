{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Simulation.Thread
    ( ThreadF(..)
    , ThreadT(..)
    , Thread
    ) where

import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Writer.Class
import Control.Monad.Trans.Free
import Data.Functor.Identity
import Data.Typeable              (Typeable)
import Simulation.Channel
import Simulation.Thread.Class
import Simulation.ThreadId
import Simulation.Time
import System.Random

data ThreadF (m :: * -> *) :: * -> * where
    GetThreadId :: (ThreadId -> a) -> ThreadF m a
    Fork        :: ThreadT m () -> (ThreadId -> a) -> ThreadF m a
    Kill        :: ThreadId -> a -> ThreadF m a
    NewChannel  :: Typeable b => (Channel b -> a) -> ThreadF m a
    Send        :: Typeable b => b -> Channel b -> a -> ThreadF m a
    Expect      :: Typeable b => Channel b -> (b -> a) -> ThreadF m a
    GetTime     :: (Seconds -> a) -> ThreadF m a
    Delay       :: Seconds -> a -> ThreadF m a
    Log         :: LogEntry ThreadId -> a -> ThreadF m a
    WithStdGen  :: (StdGen -> (b, StdGen)) -> (b -> a) -> ThreadF m a

deriving instance Functor (ThreadF m)

newtype ThreadT m a = ThreadT (FreeT (ThreadF m) m a)
    deriving (Functor, Applicative, Monad, MonadIO, MonadReader r, MonadState s, MonadWriter w)

instance MonadTrans ThreadT where
    lift = ThreadT . lift

instance Monad m => MonadThread (ThreadT m) where
    type ThreadIdT (ThreadT m) = ThreadId
    type ChannelT (ThreadT m) = Channel

    getThreadId  = ThreadT $ FreeT $ return $ Free $ GetThreadId return
    fork t       = ThreadT $ FreeT $ return $ Free $ Fork t return
    kill tid     = ThreadT $ FreeT $ return $ Free $ Kill tid (return ())
    newChannel   = ThreadT $ FreeT $ return $ Free $ NewChannel return
    send a c     = ThreadT $ FreeT $ return $ Free $ Send a c (return ())
    expect c     = ThreadT $ FreeT $ return $ Free $ Expect c return
    getTime      = ThreadT $ FreeT $ return $ Free $ GetTime return
    delay s      = ThreadT $ FreeT $ return $ Free $ Delay s (return ())
    logEntryT e  = ThreadT $ FreeT $ return $ Free $ Log e (return ())
    withStdGen f = ThreadT $ FreeT $ return $ Free $ WithStdGen f return

type Thread = ThreadT Identity
