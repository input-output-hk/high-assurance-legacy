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
    worker (cond :?: cnt)    = if eval cond then worker cnt else return ()
    worker (chan :<: val)    = putMVar (eval chan) (eval val)
    worker (chan :>: cnt)    = takeMVar (eval chan) >>= worker . cnt . Identity
    worker (prc1 :|: prc2)   = do
                                   void $ forkIO $ worker prc1
                                   void $ forkIO $ worker prc2
    worker (NewChannel cnt)  = newEmptyMVar >>= worker . cnt . Identity
    worker (Letrec defs res) = worker . res $
                               fix (map worker . defs . ensureSpine)
    worker (PVar meaning)    = meaning

    eval :: _ Identity a -> a
    eval = runIdentity . dataInter
