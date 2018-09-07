{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Ouroboros.ChiCalculus.Process.Run (

    run

) where

import Prelude hiding (map)

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (putMVar, takeMVar, newEmptyMVar)
import Control.Monad (void)

import Data.Function (fix)
import Data.Functor.Identity (Identity (..))
import Data.List.FixedLength (ensureSpine, map)

import Ouroboros.ChiCalculus.Process (Process (..), Interpretation)

run :: Interpretation Identity (IO ())
run dataInter = void . forkIO . worker

    where

    worker Stop              = return ()
    worker (Guard cond cont) = if eval cond then worker cont else return ()
    worker (chan :<: val)    = putMVar (eval chan) (eval val)
    worker (chan :>: cont)   = takeMVar (eval chan) >>= worker . cont . Identity
    worker (prc1 :|: prc2)   = do
                                   void $ forkIO $ worker prc1
                                   void $ forkIO $ worker prc2
    worker (NewChannel cont) = newEmptyMVar >>= worker . cont . Identity
    worker (Letrec defs res) = worker . res $
                               fix (map worker . defs . ensureSpine)
    worker (PVar meaning)    = meaning

    eval :: _ Identity a -> a
    eval = runIdentity . dataInter
