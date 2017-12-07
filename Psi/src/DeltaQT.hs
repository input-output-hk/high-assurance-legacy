{-# LANGUAGE UndecidableInstances #-}

module DeltaQT
    ( DeltaQT (..)
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

data DeltaQF a = Choice Probability a a | Delay a
    deriving Functor

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

type DeltaQ = DeltaQT Identity

toDeltaQM :: DeltaQ a -> DeltaQM a
toDeltaQM = iterM f . runDeltaQT
  where
    f :: DeltaQF (DeltaQM a) -> DeltaQM a
    f (Choice p x y) = weightedChoice p x y
    f (Delay x)      = vitiate (dirac 1) >> x

type DeltaQTR r m = DeltaQT (ReaderT r m)

runDeltaQTR :: Monad m => DeltaQTR r m a -> r -> DeltaQT m a
runDeltaQTR x r = DeltaQT $ hoistFreeT (`runReaderT` r) $ runDeltaQT x

type DeltaQTS s m = DeltaQT (StateT s m)

runDeltaQTS :: Monad m => DeltaQTS s m a -> s -> DeltaQT m (a, s)
runDeltaQTS x s = DeltaQT $ FreeT $ do
    (m, s') <- runStateT (runFreeT $ runDeltaQT x) s
    return $ case m of
        Pure a -> Pure (a, s')
        Free u -> Free $ (runDeltaQT . flip runDeltaQTS s' . DeltaQT) <$> u 

evalDeltaQTS :: Monad m => DeltaQTS s m a -> s -> DeltaQT m a
evalDeltaQTS x s = fst <$> runDeltaQTS x s

execDeltaQTS :: Monad m => DeltaQTS s m a -> s -> DeltaQT m s
execDeltaQTS x s = snd <$> runDeltaQTS x s
