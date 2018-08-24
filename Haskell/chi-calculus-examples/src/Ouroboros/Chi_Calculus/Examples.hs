{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TupleSections    #-}
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
    DLit :: Show a => a -> Dat d a
    DNot :: Dat d Bool -> Dat d Bool
    DVar :: d a -> Dat d a

datEval :: Data.Interpretation Dat Identity
datEval (DLit a) = Identity a
datEval (DNot b) = Identity $ not $ runIdentity $ datEval b
datEval (DVar x) = x

datExpr :: Data.Interpretation Dat (Const Text)
datExpr (DLit a) = Const $ pack $ show a
datExpr (DNot b) = Const $ pack "(not " <> getConst (datExpr b) <> pack ")"
datExpr (DVar t) = t

withLogging :: (forall c d p. (String -> Process Dat c d p) -> Process Dat c d p)
            -> ClosedProcess Dat '[String]
withLogging f = closedProcess $ \c -> f $ (c :<:) . (Uniform 0 0,) . DLit

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
deltaQIO p = runSampling $ deltaQ datEval runIdentity 10 p

delay :: DeltaQ -> Process Dat c d p -> Process Dat c d p
delay d p =
    NewChannel $ \c1 ->
    NewChannel $ \c2 ->  (c1 :<: (d, DLit "DELAY"))
                     :|: (c1 :>: const (c2 :<: (Uniform 0 0, DLit "ACK")))
                     :|: (c2 :>: const p)

ifThenElse :: Dat d Bool
           -> Process Dat c d p
           -> Process Dat c d p
           -> Process Dat c d p
ifThenElse b t e = Guard b t :|: Guard (DNot b) e

timeout :: Seconds
        -> c ()
        -> Process Dat c d p
        -> Process Dat c d p
        -> Process Dat c d p
timeout t ch p q =
    NewChannel $ \ch' ->
        (ch :>: const (ch' :<: (Uniform 0 0, DLit True)))
    :|: (ch' :<: (Uniform t t, DLit False))
    :|: (ch' :>: \b -> ifThenElse (DVar b) p q)

hello :: ClosedProcess Dat '[String]
hello = withLogging $ \log -> log "Hello, World!"

pingPong :: ClosedProcess Dat '[String]
pingPong = withLogging $ \log ->
    NewChannel $ \c ->
    NewChannel $ \d ->
            log "sending PING"
        :|: (c :<: (Uniform 1 2, DLit "PING"))
        :|: (d :>: (const $ log "received PONG"))
        :|: (c :>: (const $     log "received PING"
                            :|: (d :<: (Uniform 2 3, DLit "PONG"))))

tick :: ClosedProcess Dat '[String]
tick = withLogging $ \log ->
    Letrec @('S 'Z)
        (\xs -> (    log "tick"
                 :|: (delay (Uniform 1 1) $ Var $ xs FL.! FL.Here))
                FL.::: FL.Empty)
        (\(p FL.::: FL.Empty) -> Var p)

testTimeout :: ClosedProcess Dat '[String]
testTimeout = withLogging $ \log ->
    NewChannel $ \c ->
        (NewChannel $ \d ->
                (d :<: (Uniform 1 3, DLit ()))
            :|: (d :>: const (c :<: (Uniform 0 0, DLit ()))))
        :|: timeout 2 c (log "received") (log "timout!")

test :: ClosedProcess Dat '[String] -> IO ()
test p = do
    putStrLn $ unpack $ getConst $ interpret expr datExpr p
    putStrLn "------------------------------------"
    execWithLogging p
    putStrLn "------------------------------------"
    (e, xs) <- deltaQIO p
    print e
    print $ xs ! Here
