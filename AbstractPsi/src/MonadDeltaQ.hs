module MonadDeltaQ
    ( MonadDeltaQ (..)
    , ftf
    , ltf
    ) where

import Control.Monad

class MonadPlus m => MonadDeltaQ m where
    sync   :: m a -> m b -> m (Either (a, m b) (b, m a))

ftf :: MonadDeltaQ m => m a -> m a -> m a
ftf x y = either fst fst <$> sync x y

ltf :: MonadDeltaQ m => m a -> m b -> m (a, b)
ltf x y = do
    e <- sync x y
    case e of
        Left (a, mb)  -> mb >>= \b -> return (a, b)
        Right (b, ma) -> ma >>= \a -> return (a, b)
