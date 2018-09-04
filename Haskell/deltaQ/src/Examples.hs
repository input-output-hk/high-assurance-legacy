{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Examples where

import           Control.Monad
import           Data.DeltaQ
import           Data.List       (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Process
import           Text.Printf     (printf)

ex :: (Ord p, Fractional p) => Int -> DDQ p IntP
ex = exact . Finite . intP

un :: (Ord p, Fractional p) => Int -> Int -> DDQ p IntP
un m n = uniform (intP m) (intP n)

queue1, queue2, queue3, queue4 :: MonadDeltaQ p IntP (DDQ p IntP) m => QueueDQ m Char
queue1 = enqueueDQ (mix 0.5 never $ un 0 4)  'x' $
         enqueueDQ (ex 1)                    'a' $
         enqueueDQ (ex 3)                    'c' $
         enqueueDQ (ex 2)                    'b'
         emptyQueueDQ

queue2 = enqueueDQ (mix 0.5 never $ ex 7)    'x' $
         enqueueDQ (ex 10)                   'y' $
         enqueueDQ (mix 0.2 never $ un 3 12) 'z'
         emptyQueueDQ

queue3 = enqueueDQ (mix 0.5 never $ ex 0)    'x' $
         enqueueDQ (mix 0.5 never $ un 0 1)  'y'
         emptyQueueDQ

queue4 = enqueueDQ (un 2 7)                  'b' $
         enqueueDQ (ex 3)                    'a'
         emptyQueueDQ

sampleTest :: QueueDQ (SamplingDQT Double IntP (DDQ Double IntP) IO) Char
           -> IO [(Char, IntP)]
sampleTest = sampleQueueIO

waitUntilTwo :: MonadDeltaQ p IntP (DDQ p IntP) m => QueueDQ m Char -> m ()
waitUntilTwo = go (2 :: Int)
  where
    go 0 _ = return ()
    go n q = do
        m <- dequeueDQ q
        case m of
            Nothing      -> delay never
            Just (_, q') -> go (n - 1) q'

testIO :: QueueDQ (SamplingDQT Double IntP (DDQ Double IntP) IO) Char
       -> Int
       -> IO (Map (Ext IntP) Double)
testIO q n = do
    xs <- replicateM n oneSample
    return $ histogram xs
  where
    oneSample :: IO (Ext IntP)
    oneSample = do
        m <- runSamplingT $ runSamplingDQT (waitUntilTwo q) mempty
        return $ case m of
            Nothing     -> Infinity
            Just (_, t) -> Finite t

    histogram :: [Ext IntP] -> Map (Ext IntP) Double
    histogram xs =
        let m   = foldl' (\m' x -> M.insertWith (+) x 1 m') M.empty xs :: Map (Ext IntP) Int
            l   = fromIntegral $ length xs :: Double
            f i = fromIntegral i / l
        in  f <$> m

testProb :: (Ord p, Fractional p)
         => QueueDQ (DeltaQM p IntP (DDQ p IntP)) Char
         -> DDQ p IntP
testProb = timing . waitUntilTwo

testProbDouble :: QueueDQ (DeltaQM Double IntP (DDQ Double IntP)) Char
               -> DDQ Double IntP
testProbDouble = testProb

testProbRational :: QueueDQ (DeltaQM Rational IntP (DDQ Rational IntP)) Char
                 -> DDQ Rational IntP
testProbRational = testProb

toTreeRational :: (Ord a, Show a)
               => QueueDQ (DeltaQM Rational IntP (DDQ Rational IntP)) a
               -> QueueTree Rational (DDQ Rational IntP) a
toTreeRational = toTree

printQueue :: forall a. (Ord a, Show a)
           => QueueDQ (DeltaQM Rational IntP (DDQ Rational IntP)) a
           -> IO ()
printQueue = go 0 . toTreeRational
  where
    go :: Int -> QueueTree Rational (DDQ Rational IntP) a -> IO ()
    go _ (QT [])                   = return ()
    go n (QT ((p, dq, a, q) : xs)) = do
        replicateM_ n $ putChar ' '
        printf "(%s) %s %s\n" (show p) (show a) (show $ M.toList $ getDDQ dq)
        go (n + 4) q
        go n $ QT xs

process1, process2, process3, process4 :: Chan -> Process (DDQ Rational IntP)
process1 = const Stop

process2 ch = ch :<: (mix 0.2 never $ un 1 2, "Hello, World!")

process3 ch = (ch :<: (ex 1, "x")) :|: (ch :<: (ex 2, "y"))

process4 ch = Nu $ \ch' ->
        (ch' :<: (ex 1, "PING"))
    :|: (ch' :>: \_ -> ch :<: (ex 1, "PONG"))

testProcess :: (Chan -> Process (DDQ Rational IntP)) -> IO ()
testProcess = printQueue . toQueue
