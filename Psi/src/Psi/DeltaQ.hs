{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Psi.DeltaQ
Description : interpretation of @Psi@ in @DeltaQTS@.
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module defines a (pure) interpretation of @'Psi'@ in @'DeltaQTS'@.
-}

module Psi.DeltaQ
    ( ChanState (..)
    , CHANSTATE (..)
    , Obs
    , S (..)
    , PsiDeltaQ (..)
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

-- | The state of a channel with message type @b@.
data ChanState a b =
      Empty                                    -- ^ neither senders nor receivers
    | Sending !(NonEmpty (b, PsiDeltaQ a))     -- ^ at least one queued sender
    | Receiving !(NonEmpty (b -> PsiDeltaQ a)) -- ^ at least one queued receiver

-- | Wrapper around @'ChanState'@ to hide the message type.
data CHANSTATE a where
    CHANSTATE :: ChanState a b -> CHANSTATE a

-- | Represents a collection of observations. The value at a given time is the
-- set of all obervations made at that time.
type Obs a = Map Time (Set a)

observe' :: forall a. Ord a => Time -> a -> Obs a -> Obs a
observe' t a = M.alter f t
  where
    f :: Maybe (Set a) -> Maybe (Set a)
    f Nothing = Just $ S.singleton a
    f (Just xs) = Just $ S.insert a xs

-- | State of an abstract psi-calculus computation.
data S a = S
    { sNextChannel  :: !Int                     -- ^ number of the next unused channel
    , sTime         :: !Time                    -- ^ current time
    , sChannels     :: !(Map Int (CHANSTATE a)) -- ^ state of all used channels
    , sObservations :: !(Obs a)                 -- ^ all observations
    }

initS :: S a
initS = S
    { sNextChannel  = 1
    , sTime         = 0
    , sChannels     = M.empty
    , sObservations = M.empty
    }

-- | Interpretation of an abstract psi-calculus process as a @'MonadDeltaQ'@
-- computation.
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

-- | All observations of an abstract psi-calculus process, represented as a
-- @'DeltaQ'@ computation.
observations :: Time           -- ^ timeout
             -> PsiDeltaQ a    -- ^ psi-calculus process
             -> DeltaQ (Obs a)
observations timeout p = sObservations <$> execDeltaQTS (giveUpAfter timeout $ runPsiDeltaQ p) initS
