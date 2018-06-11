{-# LANGUAGE FlexibleContexts #-}

module Examples.PingPong
    ( pingPong
    , testPingPong
    ) where

import Simulation

pingPong :: Thread ()
pingPong = do
    logMessage "start"
    a  <- newChannel
    b  <- newChannel
    t1 <- fork $ thread a b
    t2 <- fork $ thread b a
    send "PING" a
    delay 10
    kill t1
    kill t2
    logMessage "stop"
  where
    thread :: Channel String -> Channel String -> Thread ()
    thread i o = do
        s <- expect i
        case s of
            "PING" -> logMessage "received PING, sending PONG" >> delay 1 >> send "PONG" o >> thread i o
            "PONG" -> logMessage "received PONG, sending PING" >> delay 1 >> send "PING" o >> thread i o
            _      -> logMessage ("received " ++ s)

testPingPong :: IO ()
testPingPong = simulateForIO (Just 10.001) pingPong
