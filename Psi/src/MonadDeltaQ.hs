{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : MonadDeltaQ
Description : computations that take time and can fail
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module defines a type-class for probabilistic computations
that take (probabilistic) time and can possibly fail.
It also defines various useful combinators in terms of that class.
-}

module MonadDeltaQ
    ( MonadDeltaQ (..)
    , ftf
    , giveUpAfter
    , retryForever
    , retryMany
    , ltf
    , waitAtLeast
    ) where

import Control.Applicative
import Control.Monad
import Distribution
import Numeric.Natural

-- | Computations in a monad implementing @'MonadDeltaQ'@
-- are probabilistic, take time and can fail.
class MonadPlus m => MonadDeltaQ m where

    -- | Delay a computation with /tangible/ mass.
    -- The delay can be probabilistic, but it will eventually end.
    vitiate :: DTime -> m () -- only tangible mass

    -- | Synchronize to parallel computations, giving
    -- the result of the computation that finished first
    -- and a handle on the rest of the other computation.
    sync    :: m a -> m b -> m (Either (a, m b) (b, m a))

-- | /First-to-finish synchronization/: Runs to computation in parallel and
-- returns the first result, discarding the second computation.
--
-- __Note__: The 'Alternative'-instance should be defined with  @('<|>') = 'ftf'@.
ftf :: MonadDeltaQ m => m a -> m a -> m a
ftf x y = either fst fst <$> sync x y

-- | Executes the specified computation with the specified timeout.
-- Returns @'Just'@ the result if the computation finishes in time
-- and @'Nothing'@ otherwise.
giveUpAfter :: MonadDeltaQ m => Natural -> m a -> m (Maybe a)
giveUpAfter s ma = ftf (Just <$> ma) (const Nothing <$> vitiate (dirac s))

-- | Retries the specified computation forever, using the specified timeout for
-- each try. The result is the result of the first try that succeeds.
retryForever :: forall a m. MonadDeltaQ m => m a -> Natural -> m a
retryForever ma timeout = f' empty
  where
    f' :: m a -> m a
    f' ma' = do
        e <- sync (ftf ma ma') $ vitiate $ dirac timeout
        case e of
            Left (a, _)      -> return a
            Right ((), ma'') -> f' ma''

-- | Tries the specified computation once for each element in the specified list
-- of timeouts. This list can be finite or infinite. Result is the result of the
-- first try that succeeds. The computation fails if no try succeeds.
--
-- @'retryForever'@ is a special case of @'retryMany'@:
--
-- > retryForever m = retryMany m . repeat . dirac
retryMany :: forall a m. MonadDeltaQ m => m a -> [DTime] -> m a
retryMany ma timeouts = f' timeouts empty
  where
    f' :: [DTime] -> m a -> m a
    f' []       _   = empty
    f' (t : ts) ma' = do
        e <- sync (ftf ma ma') $ vitiate t
        case e of
            Left (a, _)      -> return a
            Right ((), ma'') -> f' ts ma''

-- | /Last-to-finish synchronization/: Runs two computations in parallel,
-- returning the results of both computations as a pair of results.
ltf :: MonadDeltaQ m => m a -> m b -> m (a, b)
ltf x y = do
    e <- sync x y
    case e of
        Left (a, mb)  -> mb >>= \b -> return (a, b)
        Right (b, ma) -> ma >>= \a -> return (a, b)

-- | Runs the specified computation for /at least/
-- the specified time: If the computation finishes earlier,
-- returing the result is delayed until the time is up.
waitAtLeast :: MonadDeltaQ m => DTime -> m a -> m a
waitAtLeast s = fmap snd . ltf (vitiate s)
