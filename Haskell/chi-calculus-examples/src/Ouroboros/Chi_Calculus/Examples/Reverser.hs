{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.Chi_Calculus.Examples.Reverser (

    Data (StdInput, StdOutput, Reverse, DVar),
    eval,
    runWithStdIO,
    reverser

) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (MVar, newEmptyMVar, takeMVar, putMVar)
import Control.Monad (forever, void)

import Data.Kind (Type)

import Ouroboros.Chi_Calculus.Data (
           Interpretation
       )
import Ouroboros.Chi_Calculus.Process (
           Process (..),
           Channel,
           ClosedProcess,
           interpret,
           pfix
       )
import Ouroboros.Chi_Calculus.Process.Run (
           run,
           Value (..)
       )

data Data (d :: Type -> Type) (a :: Type) where

    StdInput  :: Data d (Channel String)

    StdOutput :: Data d (Channel String)

    Reverse   :: Data d String -> Data d String

    DVar      :: d a -> Data d a

eval :: MVar String -> MVar String -> Interpretation Data Value
eval stdInput stdOutput = worker

    where

    worker StdInput       = Value stdInput
    worker StdOutput      = Value stdOutput
    worker (Reverse str)  = Value (reverse (plainValue (worker str)))
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
