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
    delay 1
    logMessage "tick"

testTicker :: IO ()
testTicker = simulateForIO (Just 10) ticker

finiteTicker :: Seconds -> Thread ()
finiteTicker s = do
    logMessage $ "start (" ++ show s ++ ")"
    tid <- fork $ forever $ do
        delay 1
        logMessage "tick"
    delay s
    logMessage "stop"
    kill tid

testFiniteTicker :: Seconds -> IO ()
testFiniteTicker = simulateIO . finiteTicker
