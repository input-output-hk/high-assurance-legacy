{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : DeltaQT
Description : monad transformer implementation of the @MonadDeltaQ@ interface
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module provides a monad transformer for implementating the @'MonadDeltaQ'@
interface.
-}

module DeltaQT
    ( DeltaQF (..)
    , DeltaQT (..)
    , DeltaQ
    , toDeltaQM
    , DeltaQTR
    , runDeltaQTR
    , DeltaQTS
    , runDeltaQTS
    , evalDeltaQTS
    , execDeltaQTS
    ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Free
import Data.Functor.Identity
import DeltaQM
import Distribution
import MonadDeltaQ
import Probability
import WeightedChoice

-- | The monad transformer @'DeltaQT'@ is a free monad transformer over
-- functor @'DeltaQF'@.
data DeltaQF a =
      Choice Probability a a -- ^ probabilistic choice
    | Delay a                -- ^ delay by one second
    deriving Functor

-- | A monad transformer for implementing the @'MonadDeltaQ'@ interface.
-- This is the free monad transformer over functor @'DeltaQF'@.
-- It can be used to represent probabilistic computations that can fail.
-- take time and have side-effects specified by the transformed monad @m@.
--
-- __Note__: The failing computation @'empty'@ is represented by the infinitely delayed
-- computation and hence not explicitly detectable:
--
-- > empty = vitiate (dirac 1) >> empty
newtype DeltaQT m a = DeltaQT {runDeltaQT :: FreeT DeltaQF m a}
    deriving (Functor, Applicative, Monad, MonadTrans, MonadReader r, MonadState s, MonadIO, MonadFree DeltaQF)

instance Monad m => WeightedChoice (DeltaQT m a) where

    weightedChoice 0 _ y = y
    weightedChoice 1 x _ = x
    weightedChoice p x y = DeltaQT $ FreeT $ return $ Free $ Choice p (runDeltaQT x) (runDeltaQT y)

delay :: Monad m => DeltaQT m a -> DeltaQT m a
delay = (liftF (Delay ()) >>)

instance Monad m => MonadDeltaQ (DeltaQT m) where

    vitiate d = weighted $ (\(t, p) -> (fromProbability p, f t)) <$> toDiracs d
      where
        f :: Time -> DeltaQT m ()
        f 0  = return ()
        f !n = delay $ f (n - 1)

    sync x y = DeltaQT $ FreeT $ do
        u <- runFreeT $ runDeltaQT x
        case u of
            Pure a              -> return $ Pure $ Left (a, y)
            Free (Choice p s t) -> runFreeT $ runDeltaQT $ weightedChoice p
                (sync (DeltaQT s) y)
                (sync (DeltaQT t) y)
            Free (Delay d)      -> do
                let d' = DeltaQT d
                v <- runFreeT $ runDeltaQT y
                case v of
                    Pure b              -> return $ Pure $ Right (b, delay d')
                    Free (Choice p s t) -> return $ Free $ Choice p
                        (runDeltaQT $ sync (delay d') (DeltaQT s))
                        (runDeltaQT $ sync (delay d') (DeltaQT t))
                    Free (Delay e)      -> runFreeT $ runDeltaQT $ delay $ sync d' $ DeltaQT e

instance Monad m => Alternative (DeltaQT m) where
    empty = delay empty
    (<|>) = ftf

instance Monad m => MonadPlus (DeltaQT m) where

-- | The free monad over functor @'DeltaQF'@, representing probabilistic
-- computations that can fail and take time,
-- but have no other side-effects.
type DeltaQ = DeltaQT Identity

-- | Represents a computation in @'DeltaQ'@ in terms of monad @'DeltaQM'@.
--
-- __Note__: Seeing as @'empty'@ in @'DeltaQ'@ is represented as the infinitely
-- delayed computation, this function will not terminate for computations that
-- can fail. In order to handle such computations with intangible mass,
-- they should be wrapped into
-- @'giveUpAfter'@:
--
-- > toDeltaQM $ giveUpAfter 20 m
toDeltaQM :: DeltaQ a -> DeltaQM a
toDeltaQM = iterM f . runDeltaQT
  where
    f :: DeltaQF (DeltaQM a) -> DeltaQM a
    f (Choice p x y) = weightedChoice p x y
    f (Delay x)      = vitiate (dirac 1) >> x

-- | The special case of @'DeltaQT'@ with an underlying @'ReaderT'@.
type DeltaQTR r m = DeltaQT (ReaderT r m)

-- | Peels off the @'ReaderT'@ layer.
runDeltaQTR :: Monad m => DeltaQTR r m a -> r -> DeltaQT m a
runDeltaQTR x r = DeltaQT $ hoistFreeT (`runReaderT` r) $ runDeltaQT x

-- | The special case of @'DeltaQT'@ with an underlying @'StateT'@.
-- This transformer is useful for the synchronizing of state between
-- computations running in parallel (via @'sync'@).
type DeltaQTS s m = DeltaQT (StateT s m)

-- | Peels off the @'StateT'@ layer by keeping track of the state
-- as it evolves over time.
runDeltaQTS :: Monad m => DeltaQTS s m a -> s -> DeltaQT m (a, s)
runDeltaQTS x s = DeltaQT $ FreeT $ do
    (m, s') <- runStateT (runFreeT $ runDeltaQT x) s
    return $ case m of
        Pure a -> Pure (a, s')
        Free u -> Free $ (runDeltaQT . flip runDeltaQTS s' . DeltaQT) <$> u

-- | Like @'runDeltaQTS'@, but just returning the result and not the state.
evalDeltaQTS :: Monad m => DeltaQTS s m a -> s -> DeltaQT m a
evalDeltaQTS x s = fst <$> runDeltaQTS x s

-- | Like @'runDeltaQTS'@, but just returning the state and not the result.
execDeltaQTS :: Monad m => DeltaQTS s m a -> s -> DeltaQT m s
execDeltaQTS x s = snd <$> runDeltaQTS x s
