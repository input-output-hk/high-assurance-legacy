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

import Control.Monad
import Data.DeltaQ.Core
import Data.DeltaQ.Discrete
import Data.DeltaQ.IntP
import Data.DeltaQ.IntPP
import Data.DeltaQ.Monad
import Data.DeltaQ.Probability
import Data.DeltaQ.Queue

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

testIO :: Int -> IO [IntPP]
testIO n = replicateM n $ do
    m <- runSamplingT $ runSamplingDQT $ waitUntilTwo @Double testQueue
    return $ case m of
        Nothing     -> Infinity
        Just (_, t) -> Finite t

testProb :: DDQ Rational
testProb = timing $ waitUntilTwo testQueue
