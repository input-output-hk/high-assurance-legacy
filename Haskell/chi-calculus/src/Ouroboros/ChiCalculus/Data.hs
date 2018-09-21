{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.ChiCalculus.Data (

    ClosedData,
    Interpretation,
    interpret,
    VarData (dvar)

) where

import Data.Kind (Type)

type ClosedData dat
    = forall (c :: Type -> Type) (d :: Type -> Type) (a :: Type) . dat c d a

type Interpretation dat (c :: Type -> Type) (d :: Type -> Type)
    = forall a . dat c d a -> d a

interpret :: Interpretation dat c d -> ClosedData dat -> d a
interpret inter = inter

class VarData (dat :: (Type -> Type) -> (Type -> Type) -> Type -> Type) where

    dvar :: d a -> dat c d a
