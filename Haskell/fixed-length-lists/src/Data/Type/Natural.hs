{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.Type.Natural (

    Natural (Z, S),
    TypeNatural (induct)

) where

data Natural where

    Z :: Natural

    S :: Natural -> Natural

class TypeNatural n where

    induct :: f 'Z -> (forall m . f m -> f ('S m)) -> f n

instance TypeNatural 'Z where

    induct z _ = z

instance TypeNatural n => TypeNatural ('S n) where

    induct z s = s (induct z s)
