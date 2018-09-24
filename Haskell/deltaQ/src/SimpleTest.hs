module SimpleTest where

import           Control.Arrow     (first)
import           Data.DeltaQ
import           Data.DeltaQ.PList
import qualified Data.Map.Strict   as M
import           Process
import           Text.Printf       (printf)

proc :: Chan -> Process Mixed
proc logChan =
        logChan :<: (exact $ Finite 20, "A")
    :|: Nu (PrCont $ \ch ->
                ch :<: (uniformMixed 3 7, "b")
            :|: (ch :>: PrCont (const $
                    logChan :<: (exact now, "B")
                :|: logChan :<: (uniformMixed 3 7, "C"))))

runProc :: (Chan -> Process Mixed) -> [(Rational, [(Mixed, Mixed, Message)])]
runProc = map (first getProb . swap) . M.toList . runProbM . mflatten . toTrace

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

printChunk :: [(Mixed, Mixed, Message)] -> IO ()
printChunk = mapM_ $ \(Mixed mRel, Mixed mAbs, Message _ pl) ->
    printf "%s: %s\n   %s\n" pl (show mRel) (show mAbs)

runProcIO :: (Chan -> Process Mixed) -> IO ()
runProcIO = mapM_ (\(p, chunk) -> do
    print p
    printChunk chunk
    putStrLn "") . runProc
