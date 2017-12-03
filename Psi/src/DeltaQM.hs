module DeltaQM
    ( DeltaQM (..)
    , tangible
    , compact
    , toDTime
    , toPNG
    ) where

import           Control.Applicative
import           Control.Monad
import           Data.List           (foldl')
import           Data.List.NonEmpty  (NonEmpty (..), toList, fromList)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as M
import           Data.Maybe          (catMaybes, fromMaybe)
import           Data.Monoid
import           Distribution
import           MonadDeltaQ
import           Numeric.Natural
import           Probability
import           WeightedChoice

newtype DeltaQM a = DeltaQM [(a, Probability, DTime)]
    deriving Show

tangible :: DeltaQM a -> Probability
tangible (DeltaQM xs) = sum [p | (_, p, _) <- xs]

compact :: forall a. Ord a => DeltaQM a -> DeltaQM a
compact (DeltaQM xs) = DeltaQM [(a, p, d) | (a, (p, d)) <- M.toList $ foldl' f M.empty xs]
  where
    f :: Map a (Probability, DTime) -> (a, Probability, DTime) -> Map a (Probability, DTime)
    f m (a, p, d) = M.insertWith g a (p, d) m

    g :: (Probability, DTime) -> (Probability, DTime) -> (Probability, DTime)
    g (p, d) (p', d') = let p'' = p + p' in (p'', weightedChoice (probability $ fromProbability p / fromProbability p'') d d')

toDTime :: DeltaQM () -> Maybe (Probability, DTime)
toDTime m = case compact m of
    DeltaQM []           -> Nothing
    DeltaQM [((), p, d)] -> Just (p, d)
    _                    -> error "impossible branch"

toPNG :: DeltaQM () -> FilePath -> IO ()
toPNG m f = do
    let (p, d) = fromMaybe (0, dirac 0) $ toDTime m
    distToPNG p d f

instance WeightedChoice (DeltaQM a) where
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
        g :: (a -> DeltaQM b) -> (a, Probability, DTime) -> [(b, Probability, DTime)]
        g f' (a, p, d) =
            let DeltaQM ys = f' a
            in  [(b, p * q, d <> e) | (b, q, e) <- ys]

instance MonadDeltaQ DeltaQM where

    vitiate d = DeltaQM [((), 1, d)]

    sync x y = DeltaQM $ catMaybes [ h (i m n, p * q) 
                                   | (m, p) <- toList (atomize x)
                                   , (n, q) <- toList (atomize y)
                                   ]
      where
        h :: (Maybe (c, DTime), Probability) -> Maybe (c, Probability, DTime)
        h (m, p) = maybe Nothing (\(c, d) -> Just (c, p, d)) m

        i :: Maybe (a, Natural) -> Maybe (b, Natural) -> Maybe (Either (a, DeltaQM b) (b, DeltaQM a), DTime)
        i Nothing       Nothing       = Nothing
        i (Just (a, m)) Nothing       = Just (Left (a, empty), dirac m)
        i Nothing       (Just (b, n)) = Just (Right (b, empty), dirac n)
        i (Just (a, m)) (Just (b, n))
            | m <= n                  = Just (Left (a, DeltaQM [(b, 1, dirac $ n - m)]), dirac m)
            | otherwise               = Just (Right (b, DeltaQM [(a, 1, dirac $ m - n)]), dirac n)

atomize :: DeltaQM a -> NonEmpty (Maybe (a, Natural), Probability)
atomize m@(DeltaQM xs) =
    let ys = concatMap f xs
    in  if tangible m < 1 then (Nothing, 1 - tangible m) :| ys
                          else fromList ys
  where
    f :: (a, Probability, DTime) -> [(Maybe (a, Natural), Probability)]
    f (a, p, d) = [(Just (a, t), p * q) | (t, q) <- toList $ toDiracs d]



instance Alternative DeltaQM where
    empty = DeltaQM []
    (<|>) = ftf

instance MonadPlus DeltaQM
