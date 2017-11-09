{-# LANGUAGE FlexibleContexts #-}

module Examples.PingPong
    ( pingPong
    , testPingPong
    ) where

import Simulation

pingPong :: Thread ()
pingPong = do
    logEntryShow "start"
    a  <- newChannel
    b  <- newChannel
    t1 <- fork $ thread a b
    t2 <- fork $ thread b a
    send "PING" a
    delay 10000000
    kill t1
    kill t2
    logEntryShow "stop"
  where
    thread :: Channel String -> Channel String -> Thread ()
    thread i o = do
        s <- expect i
        case s of
            "PING" -> logEntryShow "received PING, sending PONG" >> delay 1000000 >> send "PONG" o >> thread i o
            "PONG" -> logEntryShow "received PONG, sending PING" >> delay 1000000 >> send "PING" o >> thread i o
            _      -> logEntryShow ("received " ++ s)

testPingPong :: IO ()
testPingPong = simulateForIO (Just 10000001) pingPong
