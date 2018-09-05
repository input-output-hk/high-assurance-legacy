{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.RModule where

import           Data.List       (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Monoid     (Sum (..))

infixr 7 -*-
infixl 6 -+-
infixl 6 -~-

class (Num r, Monoid m) => RMod r m | m -> r where
    (-*-) :: r -> m -> m
    neg :: m -> m

(-+-) :: RMod r m => m -> m -> m
(-+-) = (<>)

instance Num r => RMod r (Sum r) where

    s -*- Sum r = Sum $ s * r

    neg = negate

instance (RMod r m, RMod r n) => RMod r (m, n) where
    r -*- (x, y) = (r -*- x, r -*- y)

    neg (x, y) = (neg x, neg y)

instance RMod r m => RMod r (a -> m) where

    r -*- f = \x -> r -*- f x

    neg f = neg . f

(-~-) :: RMod r m => m -> m -> m
x -~- y = x -+- neg y

newtype FreeRMod r a = FreeRMod {runFreeRMod :: forall m. RMod r m => (a -> m) -> m}

liftRMod :: a -> FreeRMod r a
liftRMod a = FreeRMod $ \f -> f a

instance Semigroup (FreeRMod r a) where
    x <> y = FreeRMod $ \f -> runFreeRMod x f -+- runFreeRMod y f

instance Monoid (FreeRMod r a) where
    mempty = FreeRMod $ const mempty

instance Num r => RMod r (FreeRMod r a) where

    r -*- x = FreeRMod $ \f -> r -*- runFreeRMod x f

    neg x = FreeRMod $ \f -> neg $ runFreeRMod x f

newtype ExplicitFreeRMod r a = EF (Map a r)
    deriving Show

instance (Eq r, Num r, Ord a) => Semigroup (ExplicitFreeRMod r a) where
    EF m <> EF n = EF $ foldl' f m $ M.toList n
      where
        f :: Map a r -> (a, r) -> Map a r
        f m' (a, r) = M.alter (g r) a m'

        g :: r -> Maybe r -> Maybe r
        g r Nothing = Just r
        g r (Just r')
            | r + r' == 0 = Nothing
            | otherwise   = Just $ r + r'

instance (Eq r, Num r, Ord a) => Monoid (ExplicitFreeRMod r a) where
    mempty = EF M.empty

instance (Eq r, Num r, Ord a) => RMod r (ExplicitFreeRMod r a) where
    r -*- EF m = EF $ if r == 0 then mempty
                                else (* r) <$> m
    neg (EF m) = EF $ negate <$> m

explicit :: (Eq r, Num r, Ord a) => FreeRMod r a -> ExplicitFreeRMod r a
explicit x = runFreeRMod x $ \a -> EF $ M.singleton a 1

instance (Show r, Eq r, Num r, Show a, Ord a) => Show (FreeRMod r a) where
    show = show . explicit
