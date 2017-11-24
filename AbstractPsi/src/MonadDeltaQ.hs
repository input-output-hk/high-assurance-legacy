module MonadDeltaQ
    ( MonadDeltaQ (..)
    , defaultPar
    ) where

import Control.Monad

class MonadPlus m => MonadDeltaQ m where
    sync   :: m a -> m b -> m (Either (a, m b) (b, m a))

defaultPar :: MonadDeltaQ m => m a -> m a -> m a
defaultPar x y = fmap (either fst fst) $ sync x y
