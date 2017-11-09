module Examples.Ticker
    ( ticker
    , testTicker
    , finiteTicker
    , testFiniteTicker
    ) where

import Control.Monad (forever)
import Simulation

ticker :: Thread ()
ticker = forever $ do
    delay 1000000
    logEntryShow "tick"

testTicker :: IO ()
testTicker = simulateForIO (Just 10000000) ticker

finiteTicker :: Microseconds -> Thread ()
finiteTicker s = do
    logEntryShow "start"
    tid <- fork $ forever $ do
        delay 1000000
        logEntryShow "tick"
    delay s
    logEntryShow "stop"
    kill tid

testFiniteTicker :: Microseconds -> IO ()
testFiniteTicker = simulateIO . finiteTicker
