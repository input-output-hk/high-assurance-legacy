module Examples.HopByHop
    ( hopByHop
    , testHopByHop
    , hopByHopDeltaQ
    , hopByHopPNG
    ) where

import DeltaQ
import Simulation
import System.Random
import Text.Printf

data Msg = Start | Stop deriving Show

hopByHop :: Int -> Seconds -> Seconds -> Rational -> Seconds -> Int -> Thread ()
hopByHop n tMin tMax tangible timeout retry
    | n <= 1    = error "need at least two elements in the ring"
    | otherwise = do
        c1 <- newChannel
        cn <- newChannel
        _  <- fork $ link 2 c1 cn
        logMessage "start"
        observe Start
        logMessage "link 1 sends"
        send' c1
        () <- expect cn
        logMessage "stop"
        observe Stop
  where
    dq :: DeltaQ
    dq = mix (between (tMin, tMax), tangible) (bottom, 1 - tangible)

    link :: Int -> Channel () -> Channel () -> Thread ()
    link i cin cn = do
        () <- expect cin
        logMessage $ "link " ++ show i ++ " sends"
        if i == n
            then send' cn
            else do
                cout <- newChannel
                _    <- fork $ link (i + 1) cout cn
                send' cout

    send' :: Channel () -> Thread ()
    send' c = go retry
      where
        go :: Int -> Thread ()
        go 0 = logMessage "sending failed"
        go i = do
            ms <- withStdGen $ runDeltaQ dq
            case ms of
                Nothing -> delay timeout >> logMessage "retrying" >> go (i - 1)
                Just s  -> delay s >> logMessage ("sending with delay " ++ show s) >> send () c

testHopByHop :: IO ()
testHopByHop = simulateIO $ hopByHop 10 0.5 1.5 0.9 2 3

hopByHopObservable :: Observable Msg
hopByHopObservable [_]                      = Nothing
hopByHopObservable [(s, Start), (s', Stop)] = Just $ s' - s
hopByHopObservable _                        = error "impossible logs"

hopByHopDeltaQ :: Rational -> Int -> DeltaQ
hopByHopDeltaQ tangible n = observeDeltaQ (Just s) t hopByHopObservable
  where
    s :: Seconds
    s = 6 * fromRational (toRational n)

    t :: Thread ()
    t = hopByHop n 0.5 1.5 tangible 2 3

hopByHopPNG :: Int -> FilePath -> Rational -> Int -> IO ()
hopByHopPNG samples file tangible n = do
    g <- getStdGen
    let dq    = hopByHopDeltaQ tangible n
        t     = fromRational tangible :: Double
        title = printf "Ring with hop-by-hop recovery (%d links, tangible %.2f, %d samples)" n t samples
    deltaQToPNG samples g file title dq
