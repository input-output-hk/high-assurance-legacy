module Simulation.HMap
    ( IsKey(..)
    , HMap
    , empty
    , null
    , size
    , insert
    , singleton
    , lookup
    , delete
    ) where

import           Data.Typeable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Prelude         hiding (null, lookup)

class Ord (Key f) => IsKey f where
    type Key f
    key :: f a -> Key f

data HValue :: (* -> *) -> * where
    HValue :: (Typeable f, Typeable a) => f a -> HValue f

value :: Typeable a => proxy a -> HValue f -> Maybe (f a)
value _ (HValue fb) = cast fb

newtype HMap f g = HMap (Map (Key f) (HValue g))

empty :: HMap f g
empty = HMap M.empty

null :: HMap f g -> Bool
null (HMap m) = M.null m

size :: HMap f g -> Int
size (HMap m) = M.size m

insert :: (IsKey f, Typeable g, Typeable a) =>  f a -> g a -> HMap f g -> HMap f g
insert fa ga (HMap m) = HMap $ M.insert (key fa) (HValue ga) m

singleton :: (IsKey f, Typeable g, Typeable a) => f a -> g a -> HMap f g
singleton fa ga = insert fa ga empty

lookup :: (IsKey f, Typeable a) => f a -> HMap f g -> Maybe (g a)
lookup fa (HMap m) = do
    v <- M.lookup (key fa) m
    value fa v

delete :: IsKey f => f a -> HMap f g -> HMap f g
delete fa (HMap m) = HMap $ M.delete (key fa) m
