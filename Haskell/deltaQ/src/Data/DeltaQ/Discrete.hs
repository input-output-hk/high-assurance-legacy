{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.DeltaQ.Discrete
    ( DDQ (..)
    , smear
    , uniform
    , sampleDDQIO
    , sampleDDQ
    , cdf
    ) where

import           Data.DeltaQ.Core
import           Data.DeltaQ.IntP
import           Data.DeltaQ.Probability
import           Data.List               (foldl')
import           Data.Map.Strict         (Map)
import qualified Data.Map.Strict         as M

newtype DDQ p t = DDQ {getDDQ :: Map (Ext t) (Prob p)}
    deriving (Show, Eq, Ord)

smear :: forall p t.
         (Ord p, Fractional p, Time t)
      => (Ext t -> Ext t -> (Prob p, Ext t))
      -> DDQ p t
      -> DDQ p t
      -> Maybe (Prob p, DDQ p t)
smear f x y =
    let m = foldl' g M.empty [ (ps * pt, s, t)
                             | (s, ps) <- M.toList $ getDDQ x
                             , (t, pt) <- M.toList $ getDDQ y
                             ]
        p = sum $ M.elems m
    in  if p == 0 then Nothing else Just (p, DDQ $ (/ p) <$> m)
  where
    g :: Map (Ext t) (Prob p) -> (Prob p, Ext t, Ext t) -> Map (Ext t) (Prob p)
    g m (p, s, t) = case f s t of
        (q, u)
            | q > 0     -> M.insertWith (+) u (p * q) m
            | otherwise -> m

instance (Ord p, Fractional p, Time t) => Semigroup (DDQ p t) where
    x <> y = let Just (_, z) = smear (\s t -> (1, s <> t)) x y in z

instance (Ord p, Fractional p, Time t) => Monoid (DDQ p t) where
    mempty = DDQ $ M.singleton now 1

instance (Ord p, Fractional p, Time t) => DeltaQ p t (DDQ p t) where

    massive x = let m = getDDQ x in case M.lookup Infinity m of
        Nothing     -> Just (1, x)
        Just p
            | p < 1     -> let q = 1 - p in Just (q, DDQ $ (/q) <$> M.delete Infinity m)
            | otherwise -> Nothing

    exact t = DDQ $ M.singleton t 1

    mix 0 _ y = y
    mix 1 x _ = x
    mix p x y = DDQ $ M.unionWith (+) ((* p)       <$> getDDQ x)
                                      ((* (1 - p)) <$> getDDQ y)

    before = smear $ \case
        Infinity -> const (0, Infinity)
        s        -> \t -> case compare s t of
                            LT -> (1  , s)
                            EQ -> (0.5, s)
                            GT -> (0  , s)

    after = smear $ \s t -> case t of
        Infinity -> (0, Infinity)
        _        -> case compare s t of
                        LT -> (0  , s)
                        EQ -> (0.5, s)
                        GT -> (1  , s)

    maxDQ x y = let Just (_, z) = smear (\s t -> (1, max s t)) x y in z

    sampleDQ = go 1 . M.toList . getDDQ
      where
        go _ []            = return Nothing
        go 0 _             = return Nothing
        go p ((t, q) : xs) = coinM (q / p)
                                (return $ fromExt t)
                                (go (p - q) xs)

        fromExt (Finite t) = Just t
        fromExt Infinity   = Nothing

uniform :: (Ord p, Fractional p) => IntP -> IntP -> DDQ p IntP
uniform x y = case getIntP y - getIntP x + 1 of
    n
        | n <= 0    -> never
        | otherwise -> let p  = prob $ 1 / fromIntegral n
                           xs = [(Finite t, p) | t <- [x .. y]]
                       in  DDQ $ M.fromList xs

sampleDDQIO :: Time t => DDQ Double t -> IO (Maybe t)
sampleDDQIO x = sampleIO $ sampleDQ x

sampleDDQ :: Time t => Int -> DDQ Double t -> Maybe t
sampleDDQ seed x = sample seed $ sampleDQ x

cdf :: forall p. (Ord p, Fractional p) => DDQ p IntP -> [Prob p]
cdf (DDQ m) = go 0 0 $ M.toList m
  where
    go :: Int -> Prob p -> [(Ext IntP, Prob  p)] -> [Prob p]
    go _ _ []                   = []
    go t p ((Infinity, _) : xs) = go t p xs
    go t p ((Finite s, q) : xs) =
        let t' = 1 + getIntP s
            p' = p + q
        in  replicate (t' - t - 1) p ++ p' : go t' p' xs
