module Simulation.Simple
    ( simulateSimple
    , simulateSimple'
    ) where

import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Identity
import           Simulation.Thread
import           Simulation.Thread.Class

simulateSimple :: forall t m a. (MonadTrans t, Monad m, MonadThread (t m)) => ThreadT (ThreadId (t m)) (Channel (t m)) m a -> t m a
simulateSimple = iterThread f 
  where
    f :: ThreadF (ThreadId (t m)) (Channel (t m)) m (t m a) -> t m a
    f (GetThreadId k) = getThreadId >>= k
    f (Fork t' k)     = fork (simulateSimple t') >>= k
    f (Kill tid t)    = kill tid >> t
    f (NewChannel k)  = newChannel >>= k
    f (Send b c t)    = send b c >> t
    f (Expect c k)    = expect c >>= k
    f (GetTime k)     = getTime >>= k
    f (Delay s t)     = delay s >> t

simulateSimple' :: forall m a. MonadThread m => ThreadT (ThreadId m) (Channel m) m a -> m a
simulateSimple' = runIdentityT . simulateSimple
