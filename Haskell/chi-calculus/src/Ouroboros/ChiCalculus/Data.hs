{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.ChiCalculus.Data (

    ClosedData,
    Interpretation,
    interpret

) where

import Data.Kind (Type)

type ClosedData dat = forall (d :: Type -> Type) a . dat d a

type Interpretation dat d = forall a . dat d a -> d a

interpret :: Interpretation dat d -> ClosedData dat -> d a
interpret inter = inter
