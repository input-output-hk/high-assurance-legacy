module DeltaQM
    ( DeltaQM (..)
    , DeltaQ
    , runDeltaQ
    ) where

import Control.Applicative
import Control.Monad
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
    empty      = DeltaQM $ \g -> (Nothing, g)
    dq <|> dq' = DeltaQM $ \g ->
        let (mas, g')   = runDeltaQM dq g
            (mas', g'') = runDeltaQM dq' g'
        in  case (mas, mas') of
                (Nothing, Nothing)         -> (Nothing, g'')
                (Just (a, s), Nothing)     -> (Just (a, s), g'')
                (Nothing, Just (a, s))     -> (Just (a, s), g'')
                (Just (a, s), Just (b, t))
                    | s <= t               -> (Just (a, s), g'')
                    | otherwise            -> (Just (b, t), g'')

instance MonadPlus DeltaQM

-- | A value of type @'DeltaQ'@ probabilistically is either a time or
-- failure (bottom, never).
type DeltaQ = DeltaQM ()

runDeltaQ :: DeltaQ -> StdGen -> (Maybe Seconds, StdGen)
runDeltaQ dq g = case runDeltaQM dq g of
    (Nothing, g')      -> (Nothing, g')
    (Just ((), s), g') -> (Just s, g')
