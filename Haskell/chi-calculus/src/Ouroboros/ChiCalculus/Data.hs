{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.ChiCalculus.Data (

    ClosedData,
    Interpretation,
    interpret,
    VarData (dvar)

) where

import Data.Kind (Type)

type ClosedData dat = forall (d :: Type -> Type) a . dat d a

type Interpretation dat d = forall a . dat d a -> d a

interpret :: Interpretation dat d -> ClosedData dat -> d a
interpret inter = inter

class VarData dat where

    dvar :: d a -> dat d a
