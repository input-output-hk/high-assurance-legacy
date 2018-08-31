{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.DeltaQ.Discrete
    ( DDQ (..)
    , sampleDDQIO
    , sampleDDQ
    ) where

import           Data.DeltaQ.Core
import           Data.DeltaQ.IntP
import           Data.DeltaQ.IntPP
import           Data.DeltaQ.Probability
import           Data.List               (foldl')
import           Data.Map.Strict         (Map)
import qualified Data.Map.Strict         as M

newtype DDQ p = DDQ {getDDQ :: Map IntPP (Prob p)}
    deriving (Show, Eq, Ord)

instance (Ord p, Fractional p) => Semigroup (DDQ p) where
    (<>) = convolve

instance (Ord p, Fractional p) => Monoid (DDQ p) where
    mempty = exact mempty

instance (Ord p, Fractional p) => DeltaQ p IntP (DDQ p) where

    never = DDQ $ M.singleton Infinity 1

    uniform x y = case getIntP y - getIntP x + 1 of
        n
            | n <= 0    -> never
            | otherwise -> let p  = prob $ 1 / fromIntegral n
                               xs = [(Finite t, p) | t <- [x .. y]]
                           in  DDQ $ M.fromList xs

    mix 0 _ y = y
    mix 1 x _ = x
    mix p x y = DDQ $ M.unionWith (+) ((* p)       <$> getDDQ x)
                                      ((* (1 - p)) <$> getDDQ y)

    smear x f = toMaybeDDQ x g
      where
        g m t q = case f (fromIntPP t) of
            Nothing -> m
            Just y  -> M.unionWith (+) m $ (q *) <$> getDDQ y

    _ >>> Nothing = never
    x >>> Just t  = DDQ $ M.fromAscList $ map (\(s, p) -> (s <> Finite t, p)) $ M.toList $ getDDQ x

    mt <<< x = toMaybeDDQ x g
      where
        t = toIntPP mt

        g m s q
            | t > s     = m
            | otherwise = M.insert (s `subPP` t) q m

    before x mt = toMaybeDDQ x g
      where
        t = toIntPP mt

        g m s q
            | s < t     = M.insert s q         m
            | s == t    = M.insert s (0.5 * q) m
            | otherwise = m

    ftf' x y = sum [ f s t * p * q
                   | (s, p) <- M.toList $ getDDQ x
                   , (t, q) <- M.toList $ getDDQ y
                   ]
      where
        f s t
            | s < t     = 1
            | s > t     = 0
            | otherwise = 0.5

    sampleDQ = go 1 . M.toList . getDDQ
      where
        go _ []            = return Nothing
        go 0 _             = return Nothing
        go p ((t, q) : xs) = coinM (q / p)
                                (return $ fromIntPP t)
                                (go (p - q) xs)

    sub _ = subP

toIntPP :: Maybe IntP -> IntPP
toIntPP (Just t) = Finite t
toIntPP Nothing  = Infinity

fromIntPP :: IntPP -> Maybe IntP
fromIntPP (Finite t) = Just t
fromIntPP Infinity   = Nothing

toMaybeDDQ :: (Ord p, Fractional p)
           => DDQ p
           -> (Map IntPP (Prob p) -> IntPP -> Prob p -> Map IntPP (Prob p))
           -> Maybe (DDQ p)
toMaybeDDQ x f =
    let m = foldl' g M.empty $ M.toList $ getDDQ x
        p = sum $ M.elems m
    in  if p == 0 then Nothing else Just $ DDQ $ (/ p) <$> m
  where
    g !m (t, q) = f m t q

sampleDDQIO :: DDQ Double -> IO (Maybe IntP)
sampleDDQIO x = sampleIO $ sampleDQ x

sampleDDQ :: Int -> DDQ Double -> Maybe IntP
sampleDDQ seed x = sample seed $ sampleDQ x
