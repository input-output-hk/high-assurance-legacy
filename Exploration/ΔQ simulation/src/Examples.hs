module Examples
    ( module Examples.GlobalRetry
    , module Examples.HopByHop
    , module Examples.PingPong
    , module Examples.Ring
    , module Examples.Ticker
    , module Examples.Timeout
    , testAll
    , ringComparison
    ) where

import Data.Colour.Names
import DeltaQ
import Examples.GlobalRetry
import Examples.HopByHop
import Examples.PingPong
import Examples.Ring
import Examples.Ticker
import Examples.Timeout
import System.Random

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

    putStrLn "timeout (in time):"
    testTimeout 2 5
    putStrLn ""

    putStrLn "timeout (timing out):"
    testTimeout 5 2
    putStrLn ""

    putStrLn "ring"
    testRing
    putStrLn ""

    putStrLn "hop by hop recovery"
    testHopByHop
    putStrLn ""

    putStrLn "global recovery"
    testGlobalRetry

ringComparison :: Int -> FilePath -> Rational -> Int -> IO ()
ringComparison samples file tangible n = do
    let dqRing   = ringDeltaQ tangible n
        dqHop    = hopByHopDeltaQ tangible n
        dqGlobal = globalRetryDeltaQ tangible n
    g <- newStdGen
    deltaQsToPNG samples g file "Ring Comparison" [ ("no recovery", blue, dqRing)
                                                  , ("global recovery", green, dqGlobal)
                                                  , ("hop-by-hop recovery", red, dqHop)
                                                  ]
