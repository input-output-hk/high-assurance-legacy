module Examples.Ticker
    ( ticker
    , testTickerIO
    , finiteTicker
    , testFiniteTickerIO
    ) where

import Control.Monad (forever)
import Control.Monad.Trans.Class (lift)
import Simulation

ticker :: MonadThread m => (Microseconds -> m ()) -> m ()
ticker logTime = forever $ do
    delay 1000000
    t <- getTime
    logTime t

testTickerIO :: IO ()
testTickerIO = simulateSimple' $ ticker $ lift . print

finiteTicker :: MonadThread m => Microseconds -> (String -> m ()) -> m ()
finiteTicker s log' = do
    log' "start"
    tid <- fork $ forever $ do
        delay 1000000
        t <- getTime
        log' $ show t
    delay s
    log' "stop"
    kill tid

testFiniteTickerIO :: Microseconds -> IO ()
testFiniteTickerIO s = simulateSimple' $ finiteTicker s $ lift . putStrLn
