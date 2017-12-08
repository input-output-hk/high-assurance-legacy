module Psi.DeltaQ
    ( Obs
    , PsiDeltaQ
    , observations
    ) where

import           Control.Monad.State
import           Data.Functor.Const
import           Data.Functor.Identity
import           Data.List.NonEmpty    (NonEmpty (..), (<|))
import           Data.Map.Strict       (Map)
import qualified Data.Map.Strict       as M
import           Data.Set              (Set)
import qualified Data.Set              as S
import           DeltaQT
import           Distribution
import           MonadDeltaQ
import           Probability
import           Psi.Core
import           Unsafe.Coerce
import           WeightedChoice

data ChanState a b =
    Empty
    | Sending !(NonEmpty (b, PsiDeltaQ a))
    | Receiving !(NonEmpty (b -> PsiDeltaQ a))

data CHANSTATE a where
    CHANSTATE :: ChanState a b -> CHANSTATE a

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
    , sChannels     :: !(Map Int (CHANSTATE a))
    , sObservations :: !(Obs a)
    }

initS :: S a
initS = S
    { sNextChannel  = 1
    , sTime         = 0
    , sChannels     = M.empty
    , sObservations = M.empty
    }

newtype PsiDeltaQ a = PsiDeltaQ {runPsiDeltaQ :: DeltaQTS (S a) Identity ()}

getChanState :: Const Int b -> DeltaQTS (S a) Identity (ChanState a b)
getChanState c = do
    cs <- gets sChannels
    case cs M.! getConst c of
        CHANSTATE st -> return $ unsafeCoerce st

setChanState :: Const Int b -> ChanState a b -> DeltaQTS (S a) Identity ()
setChanState c st = modify $ \s -> s {sChannels = M.insert (getConst c) (CHANSTATE st) $ sChannels s}

instance Ord a => Psi (PsiDeltaQ a) where

    type Chan (PsiDeltaQ a)        = Const Int
    type Value (PsiDeltaQ a)       = Identity
    type Observation (PsiDeltaQ a) = a

    done = PsiDeltaQ $ return ()

    nu k = PsiDeltaQ $ do
        n <- gets sNextChannel
        modify $ \s -> s {sNextChannel = n + 1}
        let c = Const n
        setChanState c Empty
        runPsiDeltaQ $ k c

    inp c k = PsiDeltaQ $ do
        st <- getChanState c
        case st of
            Empty                  -> setChanState c $ Receiving $ (k . Identity) :| []
            Receiving xs           -> setChanState c $ Receiving $ (k . Identity) <| xs
            Sending ((b, p) :| xs) -> do
                setChanState c $ case xs of
                    []         -> Empty
                    (x' : xs') -> Sending (x' :| xs')
                runPsiDeltaQ $ fork p (k $ Identity b)

    out c b p = PsiDeltaQ $ do
        st <- getChanState c
        case st of
            Empty               -> setChanState c $ Sending $ (runIdentity b, p) :| []
            Sending xs          -> setChanState c $ Sending $ (runIdentity b, p) <| xs
            Receiving (k :| xs) -> do
                setChanState c $ case xs of
                    []         -> Empty
                    (k' : xs') -> Receiving (k' :| xs')
                runPsiDeltaQ $ fork p (k $ runIdentity b)

    fork p q = PsiDeltaQ $ void $ ltf (runPsiDeltaQ p) (runPsiDeltaQ q)

    observe a p = PsiDeltaQ $ do
        t   <- gets sTime
        obs <- gets sObservations
        modify $ \s -> s {sObservations = observe' t a obs}
        runPsiDeltaQ p

    delay d p = PsiDeltaQ $ weighted $ (\(t, q) -> (fromProbability q, f t)) <$> toDiracs d
      where
        f :: Time -> DeltaQTS (S a) Identity ()
        f t = do
            vitiate $ dirac t
            modify $ \s -> s {sTime = t + sTime s}
            runPsiDeltaQ p

    choice r p q = PsiDeltaQ $ weightedChoice r (runPsiDeltaQ p) (runPsiDeltaQ q)

observations :: Time -> PsiDeltaQ a -> DeltaQ (Obs a)
observations timeout p = sObservations <$> execDeltaQTS (giveUpAfter timeout $ runPsiDeltaQ p) initS
