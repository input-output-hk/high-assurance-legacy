module Psi.DeltaQ
    ( Obs
    , PsiDeltaQ
    , observations
    ) where

import           Control.Monad.State
import           Data.Functor.Const
import           Data.Functor.Identity
import           Data.Map.Strict       (Map)
import qualified Data.Map.Strict       as M
import           Data.Set              (Set)
import qualified Data.Set              as S
import           DeltaQT
import           Distribution
import           MonadDeltaQ
import           Probability
import           Psi.Core
import           WeightedChoice

data ChanState a =
    Empty

data CHANSTATE where
    CHANSTATE :: ChanState a -> CHANSTATE

type Obs a = Map Time (Set a)

observe' :: forall a. Ord a => Time -> a -> Obs a -> Obs a
observe' t a = M.alter f t
  where
    f :: Maybe (Set a) -> Maybe (Set a)
    f Nothing = Just $ S.singleton a
    f (Just xs) = Just $ S.insert a xs

data S a = S
    { sNextChannel  :: !Int
    , sTime         :: !Time
    , sChannels     :: !(Map Int CHANSTATE)
    , sObservations :: !(Obs a)
    }

initS :: S a
initS = S
    { sNextChannel  = 1
    , sTime         = 0
    , sChannels     = M.empty
    , sObservations = M.empty
    }

newtype PsiDeltaQ a = PsiDeltaQ {runPsiDeltaQ :: DeltaQTS (S a) Identity (Obs a)}

instance Ord a => Psi (PsiDeltaQ a) where

    type Chan (PsiDeltaQ a)        = Const Int
    type Value (PsiDeltaQ a)       = Identity
    type Observation (PsiDeltaQ a) = a

    done = PsiDeltaQ $ gets sObservations

    observe a p = PsiDeltaQ $ do
        t   <- gets sTime
        obs <- gets sObservations
        modify $ \s -> s {sObservations = observe' t a obs}
        runPsiDeltaQ p

    delay d p = PsiDeltaQ $ weighted $ (\(t, q) -> (fromProbability q, f t)) <$> toDiracs d
      where
        f :: Time -> DeltaQTS (S a) Identity (Obs a)
        f t = do
            vitiate $ dirac t
            modify $ \s -> s {sTime = t + sTime s}
            runPsiDeltaQ p

observations :: PsiDeltaQ a -> DeltaQ (Obs a)
observations p = evalDeltaQTS (runPsiDeltaQ p) initS
