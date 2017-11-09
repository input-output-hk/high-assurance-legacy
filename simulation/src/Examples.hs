module Examples
    ( module Examples.PingPong
    , module Examples.Ticker
    , module Examples.Timeout
    , testAll
    ) where

import Examples.PingPong
import Examples.Ticker
import Examples.Timeout

testAll :: IO ()
testAll = do
    putStrLn "ticker:"
    testTicker
    putStrLn ""

    putStrLn "finite ticker:"
    testFiniteTicker 10.01
    putStrLn ""

    putStrLn "ping pong:"
    testPingPong
    putStrLn ""

    putStrLn "test timeout (in time):"
    testTimeout 2 5
    putStrLn ""

    putStrLn "test timeout (timing out):"
    testTimeout 5 2
