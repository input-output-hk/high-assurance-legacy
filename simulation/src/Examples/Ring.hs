module Examples.Ring
    ( ring
    , testRing
    , ringPNG
    ) where

import DeltaQ
import Simulation
import System.Random
import Text.Printf

data Msg = Start | Stop deriving Show

ring :: Int -> DeltaQ -> Thread ()
ring n dq
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
    send' c = do
        ms <- withStdGen $ runDeltaQ dq
        case ms of
            Nothing -> return ()
            Just s  -> delay s >> send () c

testRing :: IO ()
testRing = simulateIO $ ring 10 $ between (1, 2)

ringObservable :: Observable Msg
ringObservable [_]                      = Nothing
ringObservable [(s, Start), (s', Stop)] = Just $ s' - s
ringObservable _                        = error "impossible logs"

ringDeltaQ :: Rational -> Int -> DeltaQ
ringDeltaQ tangible n = observeDeltaQ (Just s) t ringObservable
  where
    s :: Seconds
    s = 2 * fromRational (toRational n)

    t :: Thread ()
    t = ring n $ mix (between (0.5, 1.5), tangible) (bottom, 1 - tangible)

ringPNG :: Int -> FilePath -> Rational -> Int -> IO ()
ringPNG samples file tangible n = do
    g <- getStdGen
    let dq    = ringDeltaQ tangible n
        t     = fromRational tangible :: Double
        title = printf "Ring (%d links, tangible %.2f, %d samples)" n t samples
    deltaQToPNG samples g file title dq
