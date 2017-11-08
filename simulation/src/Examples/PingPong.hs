{-# LANGUAGE FlexibleContexts #-}

module Examples.PingPong
    ( pingPong
    , testPingPong
    ) where

import Simulation

pingPong :: forall m. MonadThreadPlus m => m ()
pingPong = do
    logEntry "start"
    a  <- newChannel
    b  <- newChannel
    t1 <- fork $ thread a b
    t2 <- fork $ thread b a
    send "PING" a
    delay 10000000
    kill t1
    kill t2
    logEntry "stop"
  where
    thread :: Channel m String -> Channel m String -> m ()
    thread i o = do
        s <- expect i
        case s of
            "PING" -> logEntry "received PING, sending PONG" >> delay 1000000 >> send "PONG" o >> thread i o
            "PONG" -> logEntry "received PONG, sending PING" >> delay 1000000 >> send "PING" o >> thread i o
            _      -> logEntry ("received " ++ s)

testPingPong :: IO ()
testPingPong = getLogsIO (Just 10000001) pingPong
