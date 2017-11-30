module DeltaQM
    ( DeltaQM (..)
    , tangible
    , compact
    , toDist
    , toPNG
    ) where

import           Control.Applicative
import           Control.Monad
import           Data.List           (foldl')
import           Data.List.NonEmpty  (NonEmpty (..), toList)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as M
import           Data.Maybe          (catMaybes, fromMaybe)
import           Data.Monoid
import           Distribution
import           MonadDeltaQ
import           Numeric.Natural
import           Probability
import           WeightedChoice

newtype DeltaQM a = DeltaQM [(a, Probability, Dist)]
    deriving Show

tangible :: DeltaQM a -> Probability
tangible (DeltaQM xs) = sum [p | (_, p, _) <- xs]

compact :: forall a. Ord a => DeltaQM a -> DeltaQM a
compact (DeltaQM xs) = DeltaQM [(a, p, d) | (a, (p, d)) <- M.toList $ foldl' f M.empty xs]
  where
    f :: Map a (Probability, Dist) -> (a, Probability, Dist) -> Map a (Probability, Dist)
    f m (a, p, d) = M.insertWith g a (p, d) m

    g :: (Probability, Dist) -> (Probability, Dist) -> (Probability, Dist)
    g (p, d) (p', d') = let p'' = p + p' in (p'', weightedChoice (probability $ fromProbability p / fromProbability p'') d d')

toDist :: DeltaQM () -> Maybe (Probability, Dist)
toDist m = case compact m of
    DeltaQM []           -> Nothing
    DeltaQM [((), p, d)] -> Just (p, d)
    _                    -> error "impossible branch"

toPNG :: DeltaQM () -> FilePath -> IO ()
toPNG m f = do
    let (p, d) = fromMaybe (0, dirac 0) $ toDist m
    distToPNG p d f

instance WeightedChoice (DeltaQM a) where
    neutral                                    = empty
    weightedChoice 0 _            x            = x
    weightedChoice 1 x            _            = x
    weightedChoice p (DeltaQM xs) (DeltaQM ys) =
        let xs' = [(a, q * p, d)       | (a, q, d) <- xs]
            ys' = [(a, q * (1 - p), d) | (a, q, d) <- ys]
        in  DeltaQM $ xs' ++ ys'

instance Functor DeltaQM where
    fmap = liftM

instance Applicative DeltaQM where
    pure  = return
    (<*>) = ap

instance Monad DeltaQM where
    return a         = DeltaQM [(a, 1, dirac 0)]
    DeltaQM xs >>= f = DeltaQM $ concatMap (g f) xs
      where
        g :: (a -> DeltaQM b) -> (a, Probability, Dist) -> [(b, Probability, Dist)]
        g f' (a, p, d) =
            let DeltaQM ys = f' a
            in  [(b, p * q, d <> e) | (b, q, e) <- ys]

instance MonadDeltaQ DeltaQM where
    vitiate d = DeltaQM [((), 1, d)]
    sync x y  = DeltaQM $ catMaybes [h (i m n, p * q) | (m, p) <- toList (f x), (n, q) <- toList (f y)]
      where
        f :: DeltaQM a -> NonEmpty (Maybe (a, Natural), Probability)
        f m@(DeltaQM xs) = (Nothing, 1 - tangible m) :| concatMap g xs

        g :: (a, Probability, Dist) -> [(Maybe (a, Natural), Probability)]
        g (a, p, d) = [(Just (a, t), p * q) | (t, q) <- toList $ diracs d]

        h :: (Maybe (c, Dist), Probability) -> Maybe (c, Probability, Dist)
        h (m, p)
            | p == 0    = Nothing
            | otherwise = maybe Nothing (\(c, d) -> Just (c, p, d)) m

        i :: Maybe (a, Natural) -> Maybe (b, Natural) -> Maybe (Either (a, DeltaQM b) (b, DeltaQM a), Dist)
        i Nothing       Nothing       = Nothing
        i (Just (a, m)) Nothing       = Just (Left (a, empty), dirac m)
        i Nothing       (Just (b, n)) = Just (Right (b, empty), dirac n)
        i (Just (a, m)) (Just (b, n))
            | m <= n                  = Just (Left (a, DeltaQM [(b, 1, dirac $ n - m)]), dirac m)
            | otherwise               = Just (Right (b, DeltaQM [(a, 1, dirac $ m - n)]), dirac n)

instance Alternative DeltaQM where
    empty = DeltaQM []
    (<|>) = ftf

instance MonadPlus DeltaQM
