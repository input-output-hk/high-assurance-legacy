{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes     #-}

module Ouroboros.Chi_Calculus.Examples where

import Control.Concurrent                  (forkIO)
import Control.Concurrent.MVar             (MVar, newEmptyMVar, putMVar,
                                            takeMVar)
import Data.Functor.Const                  (Const (..))
import Data.Functor.Identity               (Identity (..))
import Data.Text                           (Text, pack, unpack)
import Numeric.Natural                     (Natural)
import Ouroboros.Chi_Calculus.Process
import Ouroboros.Chi_Calculus.Process.Exec (exec)
import Ouroboros.Chi_Calculus.Process.Expr (expr)
import Prelude                             hiding (log)

newtype I d a = I {unI :: d a}

type ProcessExpr = Process I (Const Natural) (Const Text) Text

type ProcessExec = Process I MVar Identity (IO ())

exprWithLogging :: ((String -> ProcessExpr) -> ProcessExpr) -> String
exprWithLogging p = unpack $ expr unI $ p $ Send (Const 9999) . encode

execWithLogging :: ((String -> ProcessExec) -> ProcessExec) -> IO ()
execWithLogging p = do
    v <- newEmptyMVar
    _ <- forkIO $ exec unI (p $ Send v . I . Identity . Just) >> putMVar v Nothing
    go v
  where
    go :: MVar (Maybe String) -> IO ()
    go v = do
        m <- takeMVar v
        case m of
            Just s  -> putStrLn s >> go v
            Nothing -> return ()

encode :: String -> I (Const Text) String
encode s = I $ Const $ pack $ '"' : s ++ "\""

hello :: (String -> Process dat c d p) -> Process dat c d p
hello log = log "Hello, World!"

pingPong :: (String -> dat d String)
         -> (String -> Process dat c d p)
         -> Process dat c d p
pingPong enc log =
    NewChannel $ \c ->
    NewChannel $ \d ->
    Parallel
        (log "sending PING")
        (Parallel
            (Send c $ enc "PING")
            (Parallel
                (Receive d $ \_ -> log "received PONG")
                (Receive c $ \_ -> Parallel
                    (log "received PING")
                    (Send d $ enc "PONG"))))

testHello :: IO ()
testHello = do
    putStrLn $ exprWithLogging hello
    putStrLn "------------------------------------"
    execWithLogging hello

testPingPong :: IO ()
testPingPong = do
    putStrLn $ exprWithLogging $ pingPong encode
    putStrLn "------------------------------------"
    execWithLogging $ pingPong (I . Identity)
