module Examples.Ticker
    ( ticker
    , testTickerIO
    , finiteTicker
    , testFiniteTickerIO
    ) where

import Control.Monad (forever, forM_)
import Simulation
import System.Random

ticker :: MonadThreadPlus m => m ()
ticker = forever $ do
    delay 1000000
    logEntry "tick"

testTickerIO :: IO ()
testTickerIO = do
    let (logs, _) = getLogs (Just 10000000) (mkStdGen 123456) ticker
    forM_ logs print

finiteTicker :: MonadThreadPlus m => Microseconds -> m ()
finiteTicker s = do
    logEntry "start"
    tid <- fork $ forever $ do
        delay 1000000
        logEntry "tick"
    delay s
    logEntry "stop"
    kill tid

testFiniteTickerIO :: Microseconds -> IO ()
testFiniteTickerIO s = do
    let (logs, _) = getLogs Nothing (mkStdGen 123456) $ finiteTicker s
    forM_ logs print
