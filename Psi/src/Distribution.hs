module Distribution
    ( Dist
    , dirac
    , miracle
    , diracs
    ) where

import           Data.List           (foldl')
import           Data.List.NonEmpty  (NonEmpty (..), fromList)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as M
import           Numeric.Natural
import           Probability
import           WeightedChoice

newtype Dist = Dist (Map Natural Probability)
    deriving (Show, Eq, Ord)

dirac :: Natural -> Dist
dirac n = Dist $ M.singleton n 1

miracle :: Dist
miracle = dirac 0

instance Monoid Dist where
    mempty                   = miracle
    Dist m `mappend` Dist m' = Dist $ foldl' f M.empty
        [ (n + n', p * p') 
        | (n, p)   <- M.toList m
        , (n', p') <- M.toList m'
        ]
      where
        f :: Map Natural Probability -> (Natural, Probability) -> Map Natural Probability
        f m'' (n, p) = M.insertWith (+) n p m''

instance WeightedChoice Dist where
    neutral              = miracle
    weightedChoice 0 _        x         = x
    weightedChoice 1 x        _         = x
    weightedChoice p (Dist m) (Dist m') = Dist $
        M.unionWith (+) (M.map (* p) m) (M.map (* (1 - p)) m')

diracs :: Dist -> NonEmpty (Natural, Probability)
diracs (Dist m) = fromList $ M.toList m
