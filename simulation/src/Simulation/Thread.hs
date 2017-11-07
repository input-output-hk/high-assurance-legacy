{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Simulation.Thread
    ( ThreadF(..)
    , ThreadT(..)
    , iterThread
    ) where

import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Writer.Class
import Control.Monad.Trans.Free
import Data.Typeable              (Typeable)
import Simulation.Thread.Class
import Simulation.Time

data ThreadF threadId (channel :: * -> *) (m :: * -> *) :: * -> * where
    GetThreadId :: (threadId -> a) -> ThreadF threadId channel m a
    Fork        :: ThreadT threadId channel m () -> (threadId -> a) -> ThreadF threadId channel m a
    Kill        :: threadId -> a -> ThreadF threadId channel m a
    NewChannel  :: Typeable b => (channel b -> a) -> ThreadF threadId channel m a
    Send        :: Typeable b => b -> channel b -> a -> ThreadF threadId channel m a
    Expect      :: Typeable b => channel b -> (b -> a) -> ThreadF threadId channel m a
    GetTime     :: (Microseconds -> a) -> ThreadF threadId channel m a
    Delay       :: Microseconds -> a -> ThreadF threadId channel m a

deriving instance Functor (ThreadF threadId channel m)

newtype ThreadT threadId (channel :: * -> *) m a = ThreadT (FreeT (ThreadF threadId channel m) m a)
    deriving (Functor, Applicative, Monad)

instance MonadTrans (ThreadT threadId channel) where
    lift = ThreadT . lift

instance MonadIO m => MonadIO (ThreadT threadId channel m) where
    liftIO m = ThreadT $ FreeT $ do
        a <- liftIO m
        return $ Pure a

instance MonadReader r m => MonadReader r (ThreadT threadId channel m) where
    ask = ThreadT ask
    local f (ThreadT m) = ThreadT $ local f m

instance MonadState s m => MonadState s (ThreadT threadId channel m) where
    get = ThreadT get
    put = ThreadT . put

instance MonadWriter w m => MonadWriter w (ThreadT threadId channel m) where
    tell = ThreadT . tell
    listen (ThreadT m) = ThreadT $ listen m
    pass (ThreadT m) = ThreadT $ pass m

instance Monad m => MonadThread (ThreadT threadId channel m) where
    type ThreadId (ThreadT threadId channel m) = threadId
    type Channel (ThreadT threadId channel m) = channel

    getThreadId = ThreadT $ FreeT $ return $ Free $ GetThreadId return
    fork t      = ThreadT $ FreeT $ return $ Free $ Fork t return
    kill tid    = ThreadT $ FreeT $ return $ Free $ Kill tid (return ())
    newChannel  = ThreadT $ FreeT $ return $ Free $ NewChannel return
    send a c    = ThreadT $ FreeT $ return $ Free $ Send a c (return ())
    expect c    = ThreadT $ FreeT $ return $ Free $ Expect c return
    getTime     = ThreadT $ FreeT $ return $ Free $ GetTime return
    delay s     = ThreadT $ FreeT $ return $ Free $ Delay s (return ())

iterThread :: forall t m threadId channel a.
              (MonadTrans t, Monad m, Monad (t m))
           => (ThreadF threadId channel m (t m a) -> t m a)
           -> ThreadT threadId channel m a
           -> t m a
iterThread f (ThreadT m) = iterTM f m
