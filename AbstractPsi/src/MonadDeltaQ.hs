module MonadDeltaQ
    ( MonadDeltaQ (..)
    ) where

import Control.Monad
import DeltaQ
import Distribution

class (MonadPlus m, Distribution d) => MonadDeltaQ m d | m -> d where
    deltaQ :: m a -> DeltaQ d
