{-# LANGUAGE ScopedTypeVariables #-}

module Data.Piecewise
    ( QAlg (..)
    , Polynomial
    , constant
    , var
    , defint'
    , defint
    , Piece (..)
    , evalPiece
    , intPiece
    , Piecewise
    , pieces
    , pw
    , evalPW
    , intPW
    , meanPW
    , convolvePW
    , ftf
    , ltf
    , cdfPW
    , uniform
    ) where

import Data.Foldable                  (foldl')
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import ToySolver.Data.Polynomial

defint' :: (Eq r, QAlg r, Ord v)
        => Polynomial r v
        -> Polynomial r v
        -> Polynomial r v
        -> v
        -> Polynomial r v
defint' a b f v = s b - s a
  where
    g = integral f v
    s c = subst g $ \w -> if w == v then c else var w

defint :: (Eq r, QAlg r) => r -> r -> Polynomial r () -> r
defint a b f = eval (const 0) $ defint' (constant a) (constant b) f ()

data Piece r = Piece { pBeg :: r
                     , pEnd :: r
                     , pPol :: Polynomial r ()
                     }
    deriving (Eq, Ord)

instance (Ord r, Num r, PrettyCoeff r) => Pretty (Piece r) where
    pPrint (Piece b e p) = brackets $
                             pPrintCoeff prettyNormal 0 b
                         <+> char '-'
                         <+> pPrintCoeff prettyNormal 0 e
                         <+> char ':'
                         <+> pPrint (subst p $ const $ var X)

instance (Ord r, Num r, PrettyCoeff r) => Show (Piece r) where
    show = prettyShow

intPiece :: (Eq r, QAlg r) => Piece r -> r
intPiece p = defint (pBeg p) (pEnd p) (pPol p)

meanPiece :: (Eq r, QAlg r) => Piece r -> r
meanPiece (Piece a b p) = intPiece $ Piece a b $ p * var ()

evalPiece :: (Ord r, Num r) => r -> Piece r -> r
evalPiece r (Piece b e p)
    | b > e          = evalPiece r $ Piece e b (-p)
    | r < b || r > e = 0
    | otherwise      = eval (const r) p

newtype Piecewise r = PW {pieces :: [Piece r]}
    deriving (Show, Eq, Ord)

evalPW :: (Ord r, Num r) => r -> Piecewise r -> r
evalPW r = go . pieces
  where
    go [] = 0
    go (p@(Piece a b _) : xs)
        | r < a  = 0
        | r <= b = evalPiece r p
        | otherwise = go xs

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

instance (Ord r, QAlg r) => Semigroup (Piecewise r) where
    x <> y = foldl' (flip addPiece) x $ pieces y

instance (Ord r, QAlg r) => Monoid (Piecewise r) where
    mempty = noPiece

convolvePiece :: forall r. (Ord r, QAlg r) => Piece r -> Piece r -> Piecewise r
convolvePiece p@(Piece xa xb xp) q@(Piece ya yb yp)
    | xa + yb > xb + ya = convolvePiece q p
    | otherwise         = pw [ Piece (xa + ya) (xa + yb) p1
                             , Piece (xa + yb) (xb + ya) p2
                             , Piece (xb + ya) (xb + yb) p3
                             ]
      where
        x, t :: Bool
        x = False
        t = True

        x', t', pt, qt, pq, a1, a2, a3, b1, b2, b3 :: Polynomial r Bool
        x' = var x
        t' = var t
        pt = subst xp $ const x'
        qt = subst yp $ const $ t' - x'
        pq = pt * qt

        a1 = constant xa
        a2 = t' - constant yb
        a3 = a2
        b1 = t' - constant ya
        b2 = b1
        b3 = constant xb

        p1, p2, p3 :: Polynomial r ()
        p1 = i a1 b1
        p2 = i a2 b2
        p3 = i a3 b3

        i :: Polynomial r Bool -> Polynomial r Bool -> Polynomial r ()
        i a b = subst (defint' a b pq x) $ const $ var ()

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

convolvePW :: (Ord r, QAlg r) => Piecewise r -> Piecewise r -> Piecewise r
convolvePW x y = mconcat [convolvePiece p q | p <- pieces x, q <- pieces y]

intPW :: (Eq r, QAlg r) => Piecewise r -> r
intPW = sum . map intPiece . pieces

meanPW :: (Eq r, QAlg r, Fractional r) => Piecewise r -> r
meanPW ps = sum [meanPiece p | p <- pieces ps] / intPW ps

ftfPiece :: forall r. (Eq r, QAlg r)
         => r
         -> r
         -> Polynomial r ()
         -> Polynomial r ()
         -> Piece r
ftfPiece a b p q = Piece a b h
  where
    x, y   :: Bool
    x = False
    y = True

    x', y', p', q',pq :: Polynomial r Bool
    x' = var x
    y' = var y
    p' = subst p $ const x'
    q' = subst q $ const y'
    pq = p' * q'

    t, u :: Bool
    t = False
    u = True

    t', u', f1, f2, f, g :: Polynomial r Bool
    t' = var t
    u' = var u
    f1 = subst pq $ \c -> if c == x then t' else u'
    f2 = subst pq $ \c -> if c == y then t' else u'
    f  = f1 + f2
    g  = defint' t' (constant b) f u

    h :: Polynomial r ()
    h = subst g $ const $ var ()

ftf :: forall r. (Ord r, QAlg r) => Piecewise r -> Piecewise r -> Piecewise r
ftf x y = pw $ go (pieces x) (pieces y) (intPW x) (intPW y)
  where
    go :: [Piece r] -> [Piece r] -> r -> r -> [Piece r]
    go [] _ _ _ = []
    go _ [] _ _ = []
    go xs@(p@(Piece xa xb xp) : xs') ys@(q@(Piece ya yb yp) : ys') px py
        | xb <= ya  =
            let p' = Piece xa xb $ xp * constant py
            in  p' : go xs' ys (px - intPiece p) py
        | yb <= xa  = go ys xs py px
        | xa < ya   =
            let p1 = Piece xa ya xp
                p2 = Piece ya xb xp
            in  go (p1 : p2 : xs') ys px py
        | ya < xa   = go ys xs py px
        | xb < yb   =
            let q1 = Piece ya xb yp
                q2 = Piece xb yb yp
            in go xs (q1 : q2 : ys') px py
        | yb < xb   = go ys xs py px
        | otherwise =
            let Piece _ _ r = ftfPiece xa xb xp yp
                px'         = px - intPiece p
                py'         = py - intPiece q
                xp'         = xp * constant py'
                yp'         = yp * constant px'
                s           = Piece xa xb $ r + xp' + yp'
            in  s : go xs' ys' px' py'

ltf :: forall r. (Ord r, QAlg r) => Piecewise r -> Piecewise r -> Piecewise r
ltf x y = revPW $ revPW x `ftf` revPW y
  where
    revPiece :: Piece r -> Piece r
    revPiece (Piece a b p) = Piece (-b) (-a) $ subst p $ const $ - var ()

    revPW :: Piecewise r -> Piecewise r
    revPW = PW . reverse . map revPiece . pieces

cdfPiece :: (Eq r, QAlg r) => Piece r -> Piece r
cdfPiece (Piece a b p) = Piece a b $ defint' (constant a) (var ()) p ()

cdfPW :: (Ord r, QAlg r) => Piecewise r -> Piecewise r
cdfPW = pw . go 0 . pieces
  where
    go _ []       = []
    go c (x : xs) =
        let Piece a b p = cdfPiece x
            y           = Piece a b $ p + constant c
            c'          = evalPiece b y
        in  y : go c' xs

uniform :: (Ord r, Fractional r) => r -> r -> Piecewise r
uniform a b = pw [Piece a b $ constant (1 / (b - a))]

test :: Piecewise Rational
test =
    let u1  = uniform 1 3
        u2  = convolvePW u1 u1
        u4  = convolvePW u2 u2
        u8  = convolvePW u4 u4
        u16 = convolvePW u8 u8
    in  u16
