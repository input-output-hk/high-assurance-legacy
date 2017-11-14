module Examples.GlobalRetry
    ( globalRetry
    , testGlobalRetry
    , globalRetryDeltaQ
    , globalRetryPNG
    ) where

import Control.Monad (void)
import DeltaQ
import Simulation
import System.Random
import Text.Printf

data Msg = Start | Stop deriving Show

globalRetry :: Int -> Seconds -> Seconds -> Rational -> Int -> Thread ()
globalRetry n tMin tMax tangible retry
    | n <= 1    = error "need at least two elements in the ring"
    | otherwise = observe Start >> logMessage "start" >> go retry
  where
    go :: Int -> Thread ()
    go 0 = logMessage "failed"
    go i = do
        logMessage $ "trying " ++ show i
        c1 <- newChannel
        cn <- newChannel
        _  <- fork $ link 2 c1 cn
        logMessage "link 1 sends"
        send' c1
        mu <- expectTimeout cn timeout
        case mu of
            Nothing -> logMessage "timeout - retrying" >> go (i - 1)
            Just () -> logMessage "stop" >> observe Stop

    dq :: DeltaQ
    dq = mix (between (tMin, tMax), tangible) (bottom, 1 - tangible)

    timeout :: Seconds
    timeout = 1 + fromRational (toRational n) * tMax

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
            Nothing -> logMessage "lost message"
            Just s  -> void $ fork $ delay s >> logMessage ("sending with delay " ++ show s) >> send () c

testGlobalRetry :: IO ()
testGlobalRetry = simulateIO $ globalRetry 10 0.5 1.5 0.9 3

globalRetryObservable :: Observable Msg
globalRetryObservable [_]                      = Nothing
globalRetryObservable [(s, Start), (s', Stop)] = Just $ s' - s
globalRetryObservable _                        = error "impossible logs"

globalRetryDeltaQ :: Rational -> Int -> DeltaQ
globalRetryDeltaQ tangible n = observeDeltaQ (Just s) t globalRetryObservable
  where
    s :: Seconds
    s = 6 * fromRational (toRational n)

    t :: Thread ()
    t = globalRetry n 0.5 1.5 tangible 3

globalRetryPNG :: Int -> FilePath -> Rational -> Int -> IO ()
globalRetryPNG samples file tangible n = do
    g <- getStdGen
    let dq    = globalRetryDeltaQ tangible n
        t     = fromRational tangible :: Double
        title = printf "Ring with global recovery (%d links, tangible %.2f, %d samples)" n t samples
    deltaQToPNG samples g file title dq
