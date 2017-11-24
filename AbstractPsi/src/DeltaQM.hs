module DeltaQM
    ( DeltaQM (..)
    , dirac
    ) where

import Control.Applicative
import Control.Monad
import MonadDeltaQ
import System.Random       (StdGen)
import Time

-- | A value of type @'DeltaQM' a@ is a computation
-- that probabilistically either produces a value of type @a@
-- after a certain /time/ or fails.
newtype DeltaQM a = DeltaQM {runDeltaQM :: StdGen -> (Maybe (a, Seconds), StdGen)}

instance Functor DeltaQM where
    fmap = liftM

instance Applicative DeltaQM where
    pure  = return
    (<*>) = ap

-- | In the @'Monad'@ instance, @'return'@ is the computation that succeeds and
-- takes no time, and @(`>>=`)@ is /sequential composition/ (/convolution/).
instance Monad DeltaQM where
    return a = DeltaQM $ \g -> (Just (a, 0), g)
    dq >>= f = DeltaQM $ \g -> case runDeltaQM dq g of
        (Nothing, g')     -> (Nothing, g')
        (Just (a, s), g') -> case runDeltaQM (f a) g' of
            (Nothing, g'')     -> (Nothing, g'')
            (Just (b, t), g'') -> (Just (b, s + t), g'')

-- | In the @'Alternative'@ instance, @'empty'@ is the always failing computation (bottom, never),
-- and parallel composition is /First-to-Finish (FTF) synchronization/.
instance Alternative DeltaQM where
    empty = DeltaQM $ \g -> (Nothing, g)
    (<|>) = defaultPar

instance MonadPlus DeltaQM

dirac :: Seconds -> DeltaQM ()
dirac s = DeltaQM $ \g -> (Just ((), s), g)

instance MonadDeltaQ DeltaQM where
    sync x y = DeltaQM $ \g ->
        let (ma, g')  = runDeltaQM x g
            (mb, g'') = runDeltaQM y g'
            me        = case (ma, mb) of
                (Nothing, Nothing)         -> Nothing
                (Just (a, s), Nothing)     -> Just (Left (a, f s y), s)
                (Nothing, Just (b, t))     -> Just (Right (b, f t x), t)
                (Just (a, s), Just (b, t))
                    | s <= t               -> Just (Left (a, f s y), s)
                    | otherwise            -> Just (Right (b, f t x), t)
        in  (me, g'')
      where
        f :: forall a. Seconds -> DeltaQM a -> DeltaQM a
        f s z = DeltaQM go
          where
            go :: StdGen -> (Maybe (a, Seconds), StdGen)
            go g = case runDeltaQM z g of
                (Nothing, g')     -> (Nothing, g')
                (Just (a, t), g')
                    | t >= s      -> (Just (a, t - s), g')
                    | otherwise   -> go g'
