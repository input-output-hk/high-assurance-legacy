{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.Piecewise where

import Data.Alg
import Data.CMonoid
import Data.Foldable (foldl')
import Data.Mod
import Data.Pol

data Piece r = Piece { pBeg :: r
                     , pEnd :: r
                     , pPol :: Pol r ()
                     }
    deriving (Show, Eq, Ord)

intPiece :: Fractional r => Piece r -> r
intPiece p = defint (pBeg p) (pEnd p) (pPol p)

newtype Piecewise r = PW {pieces :: [Piece r]}
    deriving (Show, Eq, Ord)

noPiece :: Piecewise r
noPiece = PW []

addPiece :: (Ord r, Num r) => Piece r -> Piecewise r -> Piecewise r
addPiece (Piece b e p) ps
    | b == e = ps
    | b >  e = addPiece (Piece e b $ -p) ps
addPiece piece ps = PW $ clean $ go piece $ pieces ps
  where
    go x [] = [x]
    go x@(Piece b e p) xs@(y@(Piece b' e' p') : ys)
        | e <= b'            = x : xs
        | b < b'             = Piece b b' p : go (Piece b' e p) xs
        | b == b' && e <  e' = Piece b e (p + p') : Piece e e' p' : ys
        | b == b' && e == e' = Piece b e (p + p') : ys
        | b == b'            = Piece b e' (p + p') : go (Piece e' e p) ys
        | b >  b' && b <  e' = Piece b' b p' : go x (Piece b e' p' : ys)
        | otherwise          = y : go x ys

    clean []                                           = []
    clean (Piece _ _ 0 : xs)                           = clean xs
    clean xs@[_]                                       = xs
    clean (x@(Piece b e p) : xs@(Piece b' e' p' : ys))
        | e < b' || p /= p'                            = x : clean xs
        | otherwise                                    = clean $ Piece b e' p : ys

pw :: (Foldable f, Ord r, Num r) => f (Piece r) -> Piecewise r
pw = foldl' (flip addPiece) noPiece

instance (Ord r, Fractional r) => Semigroup (Piecewise r) where
    x <> y = foldl' (flip addPiece) x $ pieces y

instance (Ord r, Fractional r) => Monoid (Piecewise r) where
    mempty = noPiece

instance (Ord r, Fractional r) => CMonoid (Piecewise r) where

instance (Ord r, Fractional r) => Mod r (Piecewise r) where

    0 -*- _ = mempty
    r -*- x = PW [Piece b e (r -*- p) | Piece b e p <- pieces x]

    neg x = PW [Piece b e (neg p) | Piece b e p <- pieces x]

convolvePiece :: forall r. (Ord r, Fractional r) => Piece r -> Piece r -> Piecewise r
convolvePiece p@(Piece xa xb xp) q@(Piece ya yb yp)
    | xa + yb > xb + ya = convolvePiece q p
    | otherwise         = pw [ Piece (xa + ya) (xa + yb) p1
                             , Piece (xa + yb) (xb + ya) p2
                             , Piece (xb + ya) (xb + yb) p3
                             ]
      where
        x, t, pt, qt, pq :: Pol (Pol r ()) ()
        x  = var ()
        t  = iota $ var ()
        pt = dynpol (iota . iota) (const   x)     xp
        qt = dynpol (iota . iota) (const $ t - x) yp
        pq = pt * qt

        a1, a2, a3, b1, b2, b3, p1, p2, p3 :: Pol r ()
        a1 = iota xa
        a2 = var () - iota yb
        a3 = a2
        b1 = var () - iota ya
        b2 = b1
        b3 = iota xb
        p1 = defint' (iota . fromRational) a1 b1 pq
        p2 = defint' (iota . fromRational) a2 b2 pq
        p3 = defint' (iota . fromRational) a3 b3 pq

-- t - b >= ya => t >= b + ya => b <= t - ya
-- t - a <= yb => t <= a + yb => a >= t - yb
--
-- max (xa, t - yb) .. min (xb, t - ya)
--
-- t - yb <= xa => t <= xa + yb
-- t - ya >= xb => t >= xb + ya
--
-- IF xa + yb <= xb + ya
--
-- xa + ya .. xa + yb : xa     | t - ya
-- xa + yb .. xb + ya : t - yb | t - ya
-- xb + ya .. xb + yb : t - yb | xb

convolvePW :: (Ord r, Fractional r) => Piecewise r -> Piecewise r -> Piecewise r
convolvePW x y = mconcat [convolvePiece p q | p <- pieces x, q <- pieces y]

intPW :: Fractional r => Piecewise r -> r
intPW = sum . map intPiece . pieces

uniform :: Fractional r => r -> r -> Piece r
uniform a b = Piece a b $ iota (1 / (b - a))

test :: Piecewise Rational
test =
    let u1 = pw [uniform 1 3]
        u2 = convolvePW u1 u1
        u4 = convolvePW u2 u2
        u8 = convolvePW u4 u4
    in  u8
