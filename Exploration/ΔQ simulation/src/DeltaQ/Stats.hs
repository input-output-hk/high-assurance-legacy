{-# LANGUAGE RecordWildCards #-}

module DeltaQ.Stats
    ( Stats (..)
    , DeltaQStats (..)
    , stats
    ) where

import Control.Monad.State
import Data.List           (foldl', sort, group)
import Data.Maybe          (catMaybes, fromJust)
import DeltaQ.Core
import Simulation.Time
import System.Random       (StdGen)

data Stats = Stats
    { stMin   :: !Seconds
    , stMax   :: !Seconds
    , stMean  :: !Seconds
    , stVar   :: !(Maybe Rational)
    , stCDF   :: ![(Seconds, Rational)]
    } deriving Show

data DeltaQStats = DeltaQStats
    { dqstTangible :: !Rational
    , dqstStats    :: !(Maybe Stats)
    } deriving Show

data FoldState = FoldState
    { fsCount     :: !Int
    , fsJustCount :: !Int
    , fsMin       :: !(Maybe Seconds)
    , fsMax       :: !(Maybe Seconds)
    , fsSum       :: !Seconds
    , fsSquareSum :: !Rational
    }

initialFoldState :: FoldState
initialFoldState = FoldState
    { fsCount     = 0
    , fsJustCount = 0
    , fsMin       = Nothing
    , fsMax       = Nothing
    , fsSum       = 0
    , fsSquareSum = 0
    }

stats :: Int -> StdGen -> DeltaQ -> DeltaQStats
stats n g dq
    | n < 1     = error "DeltaQ.Stats.stats: At least one sample is needed to gather statistics."
    | otherwise = h $ foldl' f initialFoldState samples
  where
    samples :: [Maybe Seconds]
    samples = flip evalState g $ replicateM n $ state $ runDeltaQ dq

    f :: FoldState -> Maybe Seconds -> FoldState
    f fs            Nothing  = fs {fsCount = 1 + fsCount fs}
    f FoldState{..} (Just s) = FoldState
        { fsCount     = 1 + fsCount
        , fsJustCount = 1 + fsJustCount
        , fsMin       = Just . maybe s (min s) $ fsMin
        , fsMax       = Just . maybe s (max s) $ fsMax
        , fsSum       = s + fsSum
        , fsSquareSum = let s' = toRational s in s' * s' + fsSquareSum
        }

    h :: FoldState -> DeltaQStats
    h FoldState{..}
        | fsJustCount == 0 = DeltaQStats {dqstTangible = 0, dqstStats = Nothing}
        | otherwise        = DeltaQStats
            { dqstTangible = toRational fsJustCount / toRational fsCount
            , dqstStats    = Just Stats
                { stMin  = fromJust fsMin
                , stMax  = fromJust fsMax
                , stMean = fsSum / fromRational (toRational fsJustCount)
                , stVar  = if fsJustCount < 2
                    then Nothing
                    else Just $ let s = toRational fsSum
                                    c = toRational fsJustCount
                                in  (fsSquareSum - s * s / c) / (c - 1)
                , stCDF = cdf fsCount
                }
            }

    cdf :: Int -> [(Seconds, Rational)]
    cdf c = go 0 $ group $ sort $ catMaybes samples
      where
        c' :: Rational
        c' = toRational c

        go :: Int -> [[Seconds]] -> [(Seconds, Rational)]
        go _ []                 = []
        go i (xs@(s : _) : xxs) =
            let i' = i + length xs
            in  (s, toRational i' / c') : go i' xxs
        go _ ([] : _)           = error "impossible branch"


