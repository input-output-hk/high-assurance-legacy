{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeOperators  #-}

module Ouroboros.Chi_Calculus.Examples where

import           Control.Concurrent                  (forkIO, killThread)
import           Control.Concurrent.MVar             (MVar, newEmptyMVar,
                                                      takeMVar, tryReadMVar)
import           Control.Exception                   (mask_)
import           Control.Monad                       (forever)
import           Data.Functor.Const                  (Const (..))
import           Data.Functor.Identity               (Identity (..))
import           Data.Text                           (Text, pack, unpack)
import           Prelude                             hiding (log)

import qualified Ouroboros.Chi_Calculus.Data         as Data
import           Ouroboros.Chi_Calculus.Process
import           Ouroboros.Chi_Calculus.Process.Exec (exec)
import           Ouroboros.Chi_Calculus.Process.Expr (expr)

data Dat (d :: * -> *) a where
    StringDat :: String -> Dat d String

datEval :: Data.Interpretation Dat Identity
datEval (StringDat s) = Identity s

datExpr :: Data.Interpretation Dat (Const Text)
datExpr (StringDat s) = Const $ pack s

withLogging :: (forall c d p. (String -> Process Dat c d p) -> Process Dat c d p)
            -> ClosedProcess Dat '[String]
withLogging f = closedProcess $ \c -> f $ Send c . StringDat

execWithLogging :: ClosedProcess Dat '[String] -> IO ()
execWithLogging p = do
    logChan <- newEmptyMVar
    logger  <- forkIO $ forever $ takeMVar logChan >>= mask_ . putStrLn
    interpretEnv exec datEval p logChan
    wait logChan
    killThread logger
  where
    wait :: MVar String -> IO ()
    wait v = do
        m <- tryReadMVar v
        case m of
            Nothing -> return ()
            Just _  -> wait v

hello :: ClosedProcess Dat '[String]
hello = withLogging $ \log -> log "Hello, World!"

pingPong :: ClosedProcess Dat '[String]
pingPong = withLogging $ \log ->
    NewChannel $ \c ->
    NewChannel $ \d ->
    Parallel
        (log "sending PING")
        (Parallel
            (Send c $ StringDat "PING")
            (Parallel
                (Receive d $ \_ -> log "received PONG")
                (Receive c $ \_ -> Parallel
                    (log "received PING")
                    (Send d $ StringDat "PONG"))))

test :: ClosedProcess Dat '[String] -> IO ()
test p = do
    putStrLn $ unpack $ getConst $ interpret expr datExpr p
    putStrLn "------------------------------------"
    execWithLogging p
