{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Ouroboros.Chi_Calculus.Process.Run (

    run,
    Value (plainValue),
    PlainValue

) where

import Prelude hiding (map)

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (MVar, putMVar, takeMVar, newEmptyMVar)
import Control.Monad (void)

import Data.Function (fix)
import Data.List.FixedLength (map)

import Ouroboros.Chi_Calculus.Process (Process (..), Channel, Interpretation)

run :: Interpretation Value (IO ())
run dataInter = void . forkIO . worker

    where

    worker Stop              = return ()
    worker (Guard cond cont) = if eval cond then worker cont else return ()
    worker (chan :<: val)    = putMVar (eval chan) (eval val)
    worker (chan :>: cont)   = takeMVar (eval chan) >>= worker . cont . Value
    worker (prc1 :|: prc2)   = do
                                   void $ forkIO $ worker prc1
                                   void $ forkIO $ worker prc2
    worker (NewChannel cont) = newEmptyMVar >>= worker . cont . Value
    worker (Var meaning)     = meaning
    worker (Letrec defs res) = worker (res (fix (map worker . defs)))

    eval :: _ Value a -> PlainValue a
    eval = plainValue . dataInter

newtype Value a = Value { plainValue :: PlainValue a }

type family PlainValue a where
    PlainValue (Channel a) = MVar (PlainValue a)
    PlainValue a           = a
