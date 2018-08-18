{-# LANGUAGE RankNTypes #-}

module Ouroboros.Chi_Calculus.Process.Exec (

    exec

) where

import           Prelude                        hiding (map)

import           Control.Concurrent             (forkIO)
import           Control.Concurrent.MVar        (MVar, newEmptyMVar, putMVar,
                                                 takeMVar)

import           Data.Function                  (fix)
import           Data.Functor.Identity          (Identity (Identity, runIdentity))
import           Data.List.FixedLength          (map)

import           Ouroboros.Chi_Calculus.Process (Interpretation, Process (..))

exec :: Interpretation MVar Identity (IO ())
exec dataInter = worker

    where

    worker Stop                 = return ()
    worker (Send chan val)      = putMVar chan (runIdentity (dataInter val))
    worker (Receive chan cont)  = takeMVar chan >>= worker . cont . Identity
    worker (Parallel prc1 prc2) = forkIO (worker prc1) >>
                                  forkIO (worker prc2) >>
                                  return ()
    worker (NewChannel cont)    = newEmptyMVar >>= worker . cont
    worker (Var meaning)        = meaning
    worker (Letrec defs res)    = worker (res (fix (map worker . defs)))
