module Examples.Timeout
    ( timeoutT
    , testTimeout
    ) where

import Simulation

timeoutT :: Seconds -> Seconds -> Thread ()
timeoutT delay' timeout = do
    c <- newChannel
    _ <- fork $ do
        mst <- expectTimeout c timeout
        logEntryShow mst
    delay delay'
    send "TEST" c

testTimeout :: Seconds -> Seconds -> IO ()
testTimeout delay' = simulateIO . timeoutT delay'
