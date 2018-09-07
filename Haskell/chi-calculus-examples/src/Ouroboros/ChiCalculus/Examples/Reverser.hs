{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.ChiCalculus.Examples.Reverser (

    Data (StdInput, StdOutput, Reverse, DVar),
    eval,
    runWithStdIO,
    reverser

) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, takeMVar, putMVar)
import Control.Monad (forever, void)

import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)

import Ouroboros.ChiCalculus.Data (
           Interpretation
       )
import Ouroboros.ChiCalculus.Process (
           Process (..),
           Channel,
           ClosedProcess,
           interpret,
           pfix
       )
import Ouroboros.ChiCalculus.Process.Run (
           run
       )

data Data (d :: Type -> Type) (a :: Type) where

    StdInput  :: Data d (Channel String)

    StdOutput :: Data d (Channel String)

    Reverse   :: Data d String -> Data d String

    DVar      :: d a -> Data d a

eval :: Channel String -> Channel String -> Interpretation Data Identity
eval stdInput stdOutput = worker

    where

    worker StdInput       = Identity stdInput
    worker StdOutput      = Identity stdOutput
    worker (Reverse str)  = Identity (reverse (runIdentity (worker str)))
    worker (DVar meaning) = meaning

runWithStdIO :: ClosedProcess Data -> IO ()
runWithStdIO prc = do
    stdInput <- newEmptyMVar
    void $ forkIO $ forever (getLine >>= putMVar stdInput)
    stdOutput <- newEmptyMVar
    void $ forkIO $ forever (takeMVar stdOutput >>= putStrLn)
    interpret run (eval stdInput stdOutput) prc

reverser :: ClosedProcess Data
reverser = pfix $ \ prc ->
               StdInput :>: \ line ->
               (StdOutput :<: Reverse (DVar line) :|: PVar prc)
