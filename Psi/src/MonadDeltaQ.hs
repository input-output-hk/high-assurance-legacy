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

class MonadPlus m => MonadDeltaQ m where
    vitiate :: Dist -> m ()
    sync    :: m a -> m b -> m (Either (a, m b) (b, m a))

ftf :: MonadDeltaQ m => m a -> m a -> m a
ftf x y = either fst fst <$> sync x y

giveUpAfter :: MonadDeltaQ m => Natural -> m a -> m (Maybe a)
giveUpAfter s ma = ftf (const Nothing <$> vitiate (dirac s)) (Just <$> ma)

retryForever :: forall a m. MonadDeltaQ m => m a -> Natural -> m a
retryForever ma timeout = f' empty
  where
    f' :: m a -> m a
    f' ma' = do
        e <- sync (ftf ma ma') $ vitiate $ dirac timeout
        case e of
            Left (a, _)      -> return a
            Right ((), ma'') -> f' ma''

retryMany :: forall a m. MonadDeltaQ m => m a -> [Dist] -> m a
retryMany ma timeouts = f' timeouts empty
  where
    f' :: [Dist] -> m a -> m a
    f' []       _   = empty
    f' (t : ts) ma' = do
        e <- sync (ftf ma ma') $ vitiate t
        case e of
            Left (a, _)      -> return a
            Right ((), ma'') -> f' ts ma''

ltf :: MonadDeltaQ m => m a -> m b -> m (a, b)
ltf x y = do
    e <- sync x y
    case e of
        Left (a, mb)  -> mb >>= \b -> return (a, b)
        Right (b, ma) -> ma >>= \a -> return (a, b)

waitAtLeast :: MonadDeltaQ m => Dist -> m a -> m a
waitAtLeast s = fmap snd . ltf (vitiate s)
