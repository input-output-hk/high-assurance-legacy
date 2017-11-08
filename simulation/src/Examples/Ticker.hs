module Examples.Ticker
    ( ticker
    , testTicker
    , finiteTicker
    , testFiniteTicker
    ) where

import Control.Monad (forever)
import Simulation

ticker :: MonadThreadPlus m => m ()
ticker = forever $ do
    delay 1000000
    logEntry "tick"

testTicker :: IO ()
testTicker = getLogsIO (Just 10000000) ticker

finiteTicker :: MonadThreadPlus m => Microseconds -> m ()
finiteTicker s = do
    logEntry "start"
    tid <- fork $ forever $ do
        delay 1000000
        logEntry "tick"
    delay s
    logEntry "stop"
    kill tid

testFiniteTicker :: Microseconds -> IO ()
testFiniteTicker = getLogsIO Nothing . finiteTicker
