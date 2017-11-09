module Examples.Timeout
    ( timeoutT
    , testTimeout
    ) where

import Simulation

timeoutT :: Microseconds -> Microseconds -> Thread ()
timeoutT delay' timeout = do
    c <- newChannel
    _ <- fork $ do
        mst <- expectTimeout c timeout
        logEntryShow mst
    delay delay'
    send "TEST" c

testTimeout :: Microseconds -> Microseconds -> IO ()
testTimeout delay' = simulateIO . timeoutT delay'
