{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Data.DeltaQ
    ( module Data.DeltaQ.Core
    , module Data.DeltaQ.Discrete
    , module Data.DeltaQ.IntP
    , module Data.DeltaQ.IntPP
    , module Data.DeltaQ.Monad
    , module Data.DeltaQ.Probability
    ) where

import           Control.Monad
import           Data.DeltaQ.Core
import           Data.DeltaQ.Discrete
import           Data.DeltaQ.IntP
import           Data.DeltaQ.IntPP
import           Data.DeltaQ.Monad
import           Data.DeltaQ.Probability
import           Data.DeltaQ.Queue
import           Data.List               (foldl')
import           Data.Map.Strict         (Map)
import qualified Data.Map.Strict         as M

testQueue :: forall p m. MonadDeltaQ p IntP (DDQ p) m => QueueDQ m Char
testQueue =
    let ex n   = exact (intP n)            :: DDQ p
        un m n = uniform (intP m) (intP n) :: DDQ p
    in  enqueueDQ (mix 0.5 never (ex 7))    'x' $
        enqueueDQ                (ex 10)    'y' $
        enqueueDQ (mix 0.2 never (un 3 12)) 'z'
        Empty

waitUntilTwo :: MonadDeltaQ p IntP (DDQ p) m => QueueDQ m Char -> m ()
waitUntilTwo = go (2 :: Int)
  where
    go 0 _           = return ()
    go _ Empty       = delay never
    go n (Waiting m) = do
        (_, q) <- m
        go (n - 1) q

testIO :: Int -> IO (Map IntPP Double)
testIO n = do
    xs <- replicateM n oneSample
    return $ histogram xs
  where
    oneSample :: IO IntPP
    oneSample = do
        m <- runSamplingT $ runSamplingDQT $ waitUntilTwo @Double testQueue
        return $ case m of
            Nothing     -> Infinity
            Just (_, t) -> Finite t

    histogram :: [IntPP] -> Map IntPP Double
    histogram xs =
        let m   = foldl' (\m' x -> M.insertWith (+) x 1 m') M.empty xs :: Map IntPP Int
            l   = fromIntegral $ length xs :: Double
            f i = fromIntegral i / l
        in  f <$> m

testProb :: DDQ Double
testProb = timing $ waitUntilTwo testQueue
