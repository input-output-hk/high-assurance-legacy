{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.DeltaQ.Discrete
    ( DDQ (..)
    , uniform
    , sampleDDQIO
    , sampleDDQ
    , pdf
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

instance (Show p, Fractional p, Real p, Time t) => Monoid (DDQ p t) where
    mempty = DDQ $ M.singleton now 1

instance (Show p, Fractional p, Real p, Time t) => DeltaQ p t (DDQ p t) where

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

    before x ys        =
        let xs         = M.toList $ getDDQ x
            yss        = map (M.toList . getDDQ) ys
            n          = length ys
            xsyss      = [(b, cs) | b <- xs, cs <- sequence yss]
            (p, m, ms) = foldl' f (0, M.empty, replicate n M.empty) xsyss
        in  if p == 0
                then Nothing
                else Just (p, g p m, map (g p) ms)
      where
        f :: (Prob p, Map (Ext t) (Prob p), [Map (Ext t) (Prob p)])
          -> ((Ext t, Prob p), [(Ext t, Prob p)])
          -> (Prob p, Map (Ext t) (Prob p), [Map (Ext t) (Prob p)])
        f (p, m, ms) ((t, q), tqs)
            | any (\tq -> fst tq < t) tqs = (p, m, ms)
            | otherwise                   =
                let c   = prob
                        $ recip
                        $ fromIntegral
                        $ 1 + length (filter (\tq -> fst tq == t) tqs)
                    w   = c * q * product (map snd tqs)
                    p'  = p + w
                    m'  = M.insertWith (+) t w m
                    ms' = zipWith (h w t) tqs ms
                in  (p', m', ms')

        g :: Prob p -> Map (Ext t) (Prob p) -> DDQ p t
        g p m = DDQ $ (/ p) <$> m

        h :: Prob p
          -> Ext t
          -> (Ext t, Prob p)
          -> Map (Ext t) (Prob p)
          -> Map (Ext t) (Prob p)
        h w s (t, _) = M.insertWith (+) (diff' s t) w

        diff' :: Ext t -> Ext t -> Ext t
        diff' s t = let Just d = diff t s in d

    sampleDQ = go 1 . M.toList . getDDQ
      where
        go _ []            = return Nothing
        go 0 _             = return Nothing
        go p ((t, q) : xs) = coinM (q / p)
                                (return $ fromExt t)
                                (go (p - q) xs)

        fromExt (Finite t) = Just t
        fromExt Infinity   = Nothing

uniform :: (Show p, Fractional p, Real p) => IntP -> IntP -> DDQ p IntP
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

pdf :: forall p. (Ord p, Fractional p) => DDQ p IntP -> [Prob p]
pdf (DDQ m) = go 0 $ M.toList m
  where
    go :: Int -> [(Ext IntP, Prob  p)] -> [Prob p]
    go _ []                   = []
    go t ((Infinity, _) : xs) = go t xs
    go t ((Finite s, q) : xs) =
        let t' = 1 + getIntP s
        in  replicate (t' - t - 1) 0 ++ q : go t' xs

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
