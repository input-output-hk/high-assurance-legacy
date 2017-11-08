{-# LANGUAGE FlexibleContexts #-}

module Examples.PingPong
    ( pingPong
    , testPingPongIO
    , testPingPong
    ) where

import Control.Monad.Trans.Class (lift)
import Simulation

pingPong :: forall m. (MonadThread m, Show (ThreadId m)) => (String -> m ()) -> m ()
pingPong log' = do
    log' "start"
    a  <- newChannel
    b  <- newChannel
    t1 <- fork $ thread a b
    t2 <- fork $ thread b a
    send "PING" a
    delay 10000000
    kill t1
    kill t2
    log' "stop"
  where
    thread :: Channel m String -> Channel m String -> m ()
    thread i o = do
        s <- expect i
        case s of
            "PING" -> log' "received PING, sending PONG" >> delay 1000000 >> send "PONG" o >> thread i o
            "PONG" -> log' "received PONG, sending PING" >> delay 1000000 >> send "PING" o >> thread i o
            _      -> log' ("received " ++ s)

testPingPongIO :: IO ()
testPingPongIO = simulateSimple' $ pingPong $ \s -> lift $ do
    tid <- getThreadId
    putStrLn $ show tid ++ ": " ++ s

testPingPong :: IO ()
testPingPong = simulate $ pingPong $ \s -> do
    tid <- getThreadId
    ms  <- getTime
    lift $ putStrLn $ show tid ++ ": " ++ show ms ++ ": " ++ s
