{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Data.Pol
    ( Pol (..)
    , var
    , pol
    , deg
    , joinVar
    , splitVar
    , diff
    , diffEq
    , int
    , intEq
    , defint
    , defintEq
    , changeBase
    , DoubleAlgebra (..)
    , toDoubleFunc
    ) where

import Data.Alg
import Data.CMonoid
import Data.Free
import Data.Mod
import Data.Monoid     (Product (..), Sum (..))
import Numeric.Natural

newtype Pol r a = Pol {getPol :: FAlg r (FCMonoid a)}
    deriving (Show, Eq, Ord, Semigroup, Monoid, CMonoid, Num, Alg r, Mod r)

var :: a -> Pol r a
var = Pol . basis . basis

pol :: Alg r s => (a -> s) -> Pol r a -> s
pol f = free (getProduct . free (Product . f)) . getPol

eval :: Num r => (a -> r) -> Pol r a -> r
eval f = getAlgebra . pol (Algebra . f)

deg :: FCMonoid () -> Natural
deg = getSum . free (const 1)

joinVar :: a -> Pol (Pol r a) () -> Pol r a
joinVar a = getAlgebra . pol (const $ Algebra $ var a)

splitVar :: (Eq a, Num r) => a -> Pol r a -> Pol (Pol r a) ()
splitVar a = getComposedAlgebras
           . pol (\b -> ComposedAlgebras $ if b == a then var () else iota $ var b)

diff :: forall r. Num r => Pol r () -> Pol r ()
diff = Pol . toFAlg . free f . fromFAlg . getPol
  where
    f :: FCMonoid () -> FMod r (FCMonoid ())
    f m = case deg m of
            0 -> 0
            d -> fromIntegral d -*- basis (basis () ^^^ (d - 1))

diffEq :: (Eq a, Num r) => a -> Pol r a -> Pol r a
diffEq a = joinVar a . diff . splitVar a

int :: Fractional r => Pol r () -> Pol r ()
int = int' fromRational

int' :: forall r. Num r => (Rational -> r) -> Pol r () -> Pol r ()
int' fromRat = Pol . toFAlg . free f . fromFAlg . getPol
  where
    f :: FCMonoid () -> FMod r (FCMonoid ())
    f m =
        let e = 1 + deg m
            r = fromRat $ recip $ fromIntegral e
        in  r -*- basis (basis () ^^^ e)

intEq :: (Eq a, Fractional r) => a -> Pol r a -> Pol r a
intEq a = joinVar a . int' (iota . fromRational) . splitVar a

defint :: Fractional r => r -> r -> Pol r () -> r
defint a b p =
    let q = int p
    in  eval (const b) q - eval (const a) q

defintEq :: forall a r. (Eq a, Fractional r) => r -> r -> a -> Pol r a -> Pol r a
defintEq a b x p = eval' b q - eval' a q
  where
    q = intEq x p

    eval' :: r -> Pol r a -> Pol r a
    eval' c = pol $ \y -> if y == x then iota c else var y

changeBase :: Alg r s => Pol r a -> Pol s a
changeBase = getComposedAlgebras . pol (ComposedAlgebras . var)

newtype DoubleAlgebra r = DoubleAlgebra {getDoubleAlgebra :: Double}
    deriving Num

instance Real r => Alg r (DoubleAlgebra r) where
    iota = DoubleAlgebra . fromRational . toRational

toDoubleFunc :: Real r => Pol r () -> Double -> Double
toDoubleFunc p x = getDoubleAlgebra $ eval (const $ DoubleAlgebra x) q
  where
    q = changeBase p
