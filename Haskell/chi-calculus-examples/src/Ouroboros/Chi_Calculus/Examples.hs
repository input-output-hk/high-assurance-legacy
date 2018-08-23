{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Ouroboros.Chi_Calculus.Examples where

import           Control.Concurrent                           (forkIO,
                                                               killThread)
import           Control.Concurrent.MVar                      (MVar,
                                                               newEmptyMVar,
                                                               takeMVar,
                                                               tryReadMVar)
import           Control.Exception                            (mask_)
import           Control.Monad                                (forever)
import           Data.Functor.Const                           (Const (..))
import           Data.Functor.Identity                        (Identity (..))
import qualified Data.List.FixedLength                        as FL
import           Data.Text                                    (Text, pack,
                                                               unpack)
import           Data.Type.Natural
import           Prelude                                      hiding (log)

import qualified Ouroboros.Chi_Calculus.Data                  as Data
import           Ouroboros.Chi_Calculus.Process
import           Ouroboros.Chi_Calculus.Process.DeltaQ
import           Ouroboros.Chi_Calculus.Process.DeltaQ.DeltaQ
import           Ouroboros.Chi_Calculus.Process.DeltaQ.HList
import           Ouroboros.Chi_Calculus.Process.Exec          (exec)
import           Ouroboros.Chi_Calculus.Process.Expr          (expr)

data Dat (d :: * -> *) a where
    StringDat :: DeltaQ -> String -> Dat d String

datEval :: Data.Interpretation Dat Identity
datEval (StringDat _ s) = Identity s

datExpr :: Data.Interpretation Dat (Const Text)
datExpr (StringDat d s) = Const $ pack $ s ++ " [" ++ show d ++ "]"

dq :: Dat Identity a -> DeltaQ
dq (StringDat d _) = d

withLogging :: (forall c d p. (String -> Process Dat c d p) -> Process Dat c d p)
            -> ClosedProcess Dat '[String]
withLogging f = closedProcess $ \c -> f $ Send c . StringDat (Uniform 0 0)

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

deltaQIO :: ClosedProcess Dat ts -> IO (Exit, HList (ChannelLog Identity) ts)
deltaQIO p = runSampling $ deltaQ datEval dq 10 p

hello :: ClosedProcess Dat '[String]
hello = withLogging $ \log -> log "Hello, World!"

pingPong :: ClosedProcess Dat '[String]
pingPong = withLogging $ \log ->
    NewChannel $ \c ->
    NewChannel $ \d ->
    Parallel
        (log "sending PING")
        (Parallel
            (Send c $ StringDat (Uniform 1 2) "PING")
            (Parallel
                (Receive d $ \_ -> log "received PONG")
                (Receive c $ \_ -> Parallel
                    (log "received PING")
                    (Send d $ StringDat (Uniform 2 3) "PONG"))))

delay :: DeltaQ -> Process Dat c d p -> Process Dat c d p
delay d p =
    NewChannel $ \c1 ->
    NewChannel $ \c2 ->
    Parallel
        (Send c1 $ StringDat d "DELAY")
        (Parallel
            (Receive c1 $ \_ -> Send c2 (StringDat (Uniform 0 0) "ACK"))
            (Receive c2 $ \_ -> p))

tick :: ClosedProcess Dat '[String]
tick = withLogging $ \log ->
    Letrec @('S 'Z)
        (\xs -> Parallel (log "tick") (delay (Uniform 1 1) $ Var $ xs FL.! FL.Here) FL.::: FL.Empty)
        (\(p FL.::: FL.Empty) -> Var p)

test :: ClosedProcess Dat '[String] -> IO ()
test p = do
    putStrLn $ unpack $ getConst $ interpret expr datExpr p
    putStrLn "------------------------------------"
    execWithLogging p
    putStrLn "------------------------------------"
    (e, xs) <- runSampling $ deltaQ datEval dq 10 p
    print e
    print $ xs ! Here
