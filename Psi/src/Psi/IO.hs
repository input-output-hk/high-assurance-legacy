module Psi.IO
    ( Psi (..)
    ) where

import Control.Concurrent      (forkIO, threadDelay)
import Control.Concurrent.MVar
import Data.Functor.Identity
import Psi.Core

newtype PsiIO a = PsiIO {runPsiIO :: IO ()}

instance Show a => Psi (PsiIO a) where

    type Chan (PsiIO a)        = MVar
    type Value (PsiIO a)       = Identity
    type Observation (PsiIO a) = a

    done        = PsiIO $ return ()
    nu k        = PsiIO $ newEmptyMVar >>= runPsiIO . k
    inp c k     = PsiIO $ takeMVar c >>= \b -> runPsiIO (k $ Identity b)
    out c v p   = PsiIO $ putMVar c (runIdentity v) >> runPsiIO p
    fork p q    = PsiIO $ forkIO (runPsiIO p) >> runPsiIO q
    observe a p = PsiIO $ print a >> runPsiIO p
    --delay n p   = PsiIO $ threadDelay (1000000 * fromIntegral n) >> runPsiIO p
