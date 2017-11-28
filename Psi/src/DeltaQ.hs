module DeltaQ
    ( DeltaQ (..)
    , bottom
    , tangible
    , intangible
    ) where

import Distribution

data DeltaQ a = DeltaQ Rational a
    deriving Show

bottom :: Distribution a => DeltaQ a
bottom = DeltaQ 0 miracle

tangible :: DeltaQ a -> Rational
tangible (DeltaQ r _) = r

intangible :: DeltaQ a -> Rational
intangible = (1 -) . tangible

instance Distribution a => Distribution (DeltaQ a) where
    convolve (DeltaQ a x) (DeltaQ b y) = DeltaQ (a * b) $ convolve x y
    choice p (DeltaQ a x) (DeltaQ b y) = DeltaQ (1 - p * (1 - a) - (1 - p) * (1 - b)) $ 
                                                weighted [(p * a, x), ((1 - p) * b, y)]
    dirac                              = DeltaQ 1 . dirac
    uniform                            = DeltaQ 1 . uniform
    ftf      (DeltaQ a x) (DeltaQ b y) = DeltaQ (1 - (1 - a) * (1 - b)) (ftf x y)
