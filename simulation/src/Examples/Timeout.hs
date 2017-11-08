module Examples.Timeout
    ( timeoutT
    , testTimeout
    ) where

import Control.Monad.Trans.Class
import Simulation

timeoutT :: Microseconds -> Microseconds -> M IO ()
timeoutT delay' timeout = do
    c <- newChannel
    _ <- fork $ do
        mst <- expectTimeout c timeout
        lift $ print mst
    delay delay'
    send "TEST" c

testTimeout :: Microseconds -> Microseconds -> IO ()
testTimeout delay' = simulate . timeoutT delay'
