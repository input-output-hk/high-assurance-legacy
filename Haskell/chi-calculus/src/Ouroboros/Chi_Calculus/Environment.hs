{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Ouroboros.Chi_Calculus.Environment
    ( Env' (..)
    , Env
    , ToFromEnv (..)
    , mapEnv'
    ) where

data Env' a f xs where
    Nil  :: a -> Env' a f '[]
    Cons :: (f x -> Env' a f xs) -> Env' a f (x ': xs)

mapEnv' :: (a -> b) -> Env' a f xs -> Env' b f xs
mapEnv' g (Nil a)  = Nil $ g a
mapEnv' g (Cons h) = Cons $ mapEnv' g . h

type family Env a f xs where
    Env a f '[]       = a
    Env a f (x ': xs) = f x -> Env a f xs

class ToFromEnv xs where
    toEnv :: Env' a f xs -> Env a f xs
    fromEnv :: Env a f xs -> Env' a f xs

instance ToFromEnv '[] where
    toEnv (Nil a) = a
    fromEnv = Nil

instance ToFromEnv xs => ToFromEnv (x ': xs) where
    toEnv (Cons g) = toEnv . g
    fromEnv g = Cons $ fromEnv . g
