{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Util (
    -- * Additional generics-sop combinators
    fromHomSum
  , toHomProd
  , Rotate
  , rotate
  , unrotate
  , toSingletonPOP
  , fromSingletonSOP
    -- * Misc
  , intercalate
  , allEqualTo
    -- * TeX support
  , Equation(..)
  , Verbatim(..)
  , showVerbatim
  ) where

import Data.String
import Generics.SOP

{-------------------------------------------------------------------------------
  Additional generics-sop combinators
-------------------------------------------------------------------------------}

fromHomSum :: forall x f xs . (All ((~) x) xs) => NS f xs -> f x
fromHomSum = hcollapse . hcmap (Proxy @((~) x)) K

toHomProd :: [f x] -> (forall xs . (All ((~) x) xs) => NP f xs -> r) -> r
toHomProd []       k = k Nil
toHomProd (x : xs) k = toHomProd xs $ \ np -> k (x :* np)

type family Rotate (xs :: [*]) :: [[*]] where
  Rotate '[]       = '[]
  Rotate (x ': xs) = '[x] ': Rotate xs

rotate :: NP f xs -> (SListI2 (Rotate xs) => NP (NP f) (Rotate xs) -> b) -> b
rotate Nil       k = k $ Nil
rotate (x :* xs) k = rotate xs $ \xss -> k $ ((x :* Nil) :* xss)

unrotate :: SListI xs => NS (NP f) (Rotate xs) -> NS f xs
unrotate = go sList
  where
    go :: SList xs -> NS (NP f) (Rotate xs) -> NS f xs
    go SNil  ns             = case ns of {}
    go SCons (Z (x :* Nil)) = Z x
    go SCons (S ns)         = S (go sList ns)

toSingletonPOP :: f x -> POP f '[ '[ x ] ]
toSingletonPOP x = POP ((x :* Nil) :* Nil)

fromSingletonSOP :: SOP f '[ '[ x ] ] -> f x
fromSingletonSOP (SOP (Z (x :* Nil))) = x
fromSingletonSOP _ = error "unreachable"

{-------------------------------------------------------------------------------
  Misc
-------------------------------------------------------------------------------}

intercalate :: Monoid a => a -> [a] -> a
intercalate _   []       = mempty
intercalate _   [x]      = x
intercalate sep (x:y:zs) = x `mappend` sep `mappend` intercalate sep (y:zs)

allEqualTo :: Eq a => [a] -> Maybe a
allEqualTo []     = Nothing
allEqualTo (x:xs) = if all (== x) xs then Just x else Nothing

{-------------------------------------------------------------------------------
  TeX support
-------------------------------------------------------------------------------}

newtype Equation = Equation String

instance Show Equation where
  show (Equation tex) = "\\begin{equation*}" ++ tex ++ "\\end{equation*}"

instance Monoid Equation where
  mempty = Equation ""
  Equation a `mappend` Equation b = Equation (a ++ b)

instance IsString Equation where
  fromString = Equation

newtype Verbatim = Verbatim String

instance Show Verbatim where
  show (Verbatim tex) = "\\begin{verbatim}" ++ tex ++ "\\end{verbatim}"

instance Monoid Verbatim where
  mempty = Verbatim ""
  Verbatim a `mappend` Verbatim b = Verbatim (a ++ b)

instance IsString Verbatim where
  fromString = Verbatim

showVerbatim :: Show a => a -> Verbatim
showVerbatim = Verbatim . show
