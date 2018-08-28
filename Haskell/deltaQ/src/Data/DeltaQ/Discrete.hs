{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.DeltaQ.Discrete where

import           Data.DeltaQ.Core
import           Data.DeltaQ.IntP
import           Data.DeltaQ.Probability
import           Data.List               (foldl')
import           Data.Map.Strict         (Map)
import qualified Data.Map.Strict         as M

newtype DDQ a = DDQ {getDDQ :: Map IntP (Prob a)}
    deriving Show

mass :: (Ord a, Fractional a) => DDQ a -> Prob a
mass (DDQ m) = complementP $ M.findWithDefault impossibleP Infinity m

never :: (Ord a, Fractional a) => DDQ a
never = DDQ $ M.singleton Infinity certainP

uniform :: (Ord a, Fractional a) => Int -> Int -> DDQ a
uniform x y = go (max x 0) (max y 0)
  where
    go x' y'
        | x' > y'   = never
        | otherwise = let n  = y' - x' + 1
                          w  = recip $ fromIntegral n
                          xs = [(Finite t, prob w) | t <- [x' .. y']]
                      in  DDQ $ M.fromList xs

exact :: (Ord a, Fractional a) => Int -> DDQ a
exact t = uniform t t

fantasy :: (Ord a, Fractional a) => DDQ a
fantasy = exact 0

mix :: (Ord a, Fractional a) => Prob a -> DDQ a -> DDQ a -> DDQ a
mix p x y
    | isImpossibleP p = y
    | isCertainP p    = x
    | otherwise       = DDQ $ M.unionWith addP (mulP p               <$> getDDQ x)
                                               (mulP (complementP p) <$> getDDQ y)

instance (Ord a, Fractional a) => Semigroup (DDQ a) where
    x <> y = DDQ $ foldl' f M.empty [ (s <> t, p `mulP` q)
                                    | (s, p) <- M.toList $ getDDQ x
                                    , (t, q) <- M.toList $ getDDQ y
                                    ]
      where
        f m (t, p) = M.insertWith addP t p m

instance (Ord a, Fractional a) => Monoid (DDQ a) where
    mempty = fantasy

instance (Ord a, Fractional a) => DeltaQ a (DDQ a) where

    before x y = foldl' addP impossibleP [ p `mulP` q `mulP` f s t
                                         | (s, p) <- M.toList $ getDDQ x
                                         , (t, q) <- M.toList $ getDDQ y
                                         ]
      where
        f Infinity _    = impossibleP
        f s        t
            | s < t     = certainP
            | s > t     = impossibleP
            | otherwise = halfP

        halfP = prob 0.5

    residuum x y =
        let m = foldl' f M.empty [ (s, p, t, q)
                                 | (s, p) <- M.toList $ getDDQ x
                                 , (t, q) <- M.toList $ getDDQ y
                                 ]
            r = foldl' addP impossibleP $ M.elems m
        in  case recipP r of
                Nothing -> Nothing
                Just v  -> Just $ DDQ $ mulP v <$> m
      where
        f m (Infinity    , _, _, _) = m
        f m (s@(Finite n), p, t, q)
            | s > t             = m
            | s < t             = g m (t `subP` n) $ p `mulP` q
            | otherwise         = g m (t `subP` n) $ p `mulP` q `mulP` halfP

        halfP = prob 0.5

        g m t p = M.insertWith addP t p m
