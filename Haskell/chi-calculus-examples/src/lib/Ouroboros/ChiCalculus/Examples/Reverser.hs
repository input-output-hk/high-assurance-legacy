{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Ouroboros.ChiCalculus.Examples.Reverser (

    Data (Reverse, StdInput, StdOutput, DVar),
    eval,
    runWithStdIO,
    reverser

) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, takeMVar, putMVar)
import Control.Monad (forever, void)

import Data.Functor.Identity (Identity (..))

import Ouroboros.ChiCalculus.Data (
           Interpretation
       )
import Ouroboros.ChiCalculus.Process (
           Process (..),
           ClosedProcess,
           interpret,
           pfix
       )
import Ouroboros.ChiCalculus.Process.Run (
           run
       )

data Data c d a where

    Reverse   :: Data c d String -> Data c d String

    StdInput  :: Data c d (c String)

    StdOutput :: Data c d (c String)

    DVar      :: d a -> Data c d a

eval :: forall c . c String -> c String -> Interpretation Data c Identity
eval stdInput stdOutput = worker

    where

    worker :: Interpretation Data c Identity
    worker (Reverse str)  = Identity $ reverse (runIdentity (worker str))
    worker StdInput       = Identity $ stdInput
    worker StdOutput      = Identity $ stdOutput
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
