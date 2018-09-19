{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.Polynomial.Piecewise
    ( QAlg (..)
    , Polynomial
    , constant
    , var
    , free
    , defint'
    , defint
    , Piece (..)
    , evalPiece
    , intPiece
    , Piecewise
    , pieces
    , pw
    , mapPW
    , evalPW
    , uniformPW
    ) where

import Data.Foldable                  (foldl')
import Data.Monoid                    (Sum (..))
import Data.Polynomial.Class
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import ToySolver.Data.Polynomial

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

newtype Piecewise r = PW {pieces :: [Piece r]}
    deriving (Show, Eq, Ord)

instance (Ord r, QAlg r) => Semigroup (Piecewise r) where
    x <> y = foldl' (flip addPiece) x $ pieces y

instance (Ord r, QAlg r) => Monoid (Piecewise r) where
    mempty = PW []

instance (Ord r, QAlg r, Fractional r) => Distribution r r (Piecewise r) where

    mass = sum . map intPiece . pieces

    mean ps = case mass ps of
        0 -> Nothing
        m -> Just $ sum [meanPiece p | p <- pieces ps] / m

    support (PW [])                   = Nothing
    support (PW ps@(Piece a _ _ : _)) = let Piece _ b _ = last ps in Just (a, b)

    scale = mapPW . scalePiece

    shift = mapPW . shiftPiece

    convolve x y = mconcat [convolvePiece p q | p <- pieces x, q <- pieces y]

    before x y = pw $ go (pieces x) (pieces y) (mass x) (mass y)
      where
        go :: [Piece r] -> [Piece r] -> r -> r -> [Piece r]
        go [] _ _ _ = []
        go _ [] _ _ = []
        go xs@(p@(Piece xa xb xp) : xs') ys@(q@(Piece ya yb yp) : ys') px py
            | xb <= ya  =
                let p' = Piece xa xb $ xp * constant py
                in  p' : go xs' ys (px - intPiece p) py
            | yb <= xa  = go xs ys' px (py - intPiece q)
            | xa < ya   =
                let p1 = Piece xa ya xp
                    p2 = Piece ya xb xp
                in  go (p1 : p2 : xs') ys px py
            | ya < xa   =
                let q1 = Piece ya xa yp
                    q2 = Piece xa yb yp
                in  go xs (q1 : q2 : ys') px py
            | xb < yb   =
                let q1 = Piece ya xb yp
                    q2 = Piece xb yb yp
                in  go xs (q1 : q2 : ys') px py
            | yb < xb   =
                let p1 = Piece xa yb xp
                    p2 = Piece yb xb xp
                in  go (p1 : p2 : xs') ys px py
            | otherwise =
                let Piece _ _ r = beforePiece xa xb xp yp
                    px'         = px - intPiece p
                    py'         = py - intPiece q
                    xp'         = xp * constant py'
                    s           = Piece xa xb $ r + xp'
                in  s : go xs' ys' px' py'

    residual x y = go (pieces x) (pieces y)
      where
        go :: [Piece r] -> [Piece r] -> Piecewise r
        go [] _ = mempty
        go _ [] = mempty
        go xs@(p@(Piece xa xb xp) : xs') ys@(Piece ya yb yp : ys')
            | xb <= ya  = foldMap (residualPiece' p) ys <> go xs' ys
            | yb <= xa  = go xs ys'
            | xa < ya   =
                let p1 = Piece xa ya xp
                    p2 = Piece ya xb xp
                in  go (p1 : p2 : xs') ys
            | ya < xa   =
                let q1 = Piece ya xa yp
                    q2 = Piece xa yb yp
                in  go xs (q1 : q2 : ys')
            | xb < yb   =
                let q1 = Piece ya xb yp
                    q2 = Piece xb yb yp
                in  go xs (q1 : q2 : ys')
            | yb < xb   =
                let p1 = Piece xa yb xp
                    p2 = Piece yb xb xp
                in  go (p1 : p2 : xs') ys
            | otherwise =
                let r = pw [residualPiece xa xb xp yp]
                in  r <> go xs ys'

    endingAt t = pw . go . pieces
      where
        go []                     = []
        go (x@(Piece a b p) : xs)
            | t <= a              = []
            | t >= b              = x : go xs
            | otherwise           = [Piece a t p]

    revTime = PW . reverse . map revTimePiece . pieces

    cdf ps = getSum . foldMap (\p -> Sum . cdfPiece p) (pieces ps)

intPiece :: (Eq r, QAlg r) => Piece r -> r
intPiece p = defint (pBeg p) (pEnd p) (pPol p)

meanPiece :: (Eq r, QAlg r) => Piece r -> r
meanPiece (Piece a b p) = intPiece $ Piece a b $ p * var ()

evalPiece :: (Ord r, Num r) => r -> Piece r -> r
evalPiece r (Piece b e p)
    | b > e          = evalPiece r $ Piece e b (-p)
    | r < b || r > e = 0
    | otherwise      = eval (const r) p

evalPW :: (Ord r, Num r) => r -> Piecewise r -> r
evalPW r = go . pieces
  where
    go [] = 0
    go (p@(Piece a b _) : xs)
        | r < a  = 0
        | r <= b = evalPiece r p
        | otherwise = go xs

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

pw :: (Foldable f, Ord r, QAlg r) => f (Piece r) -> Piecewise r
pw = foldl' (flip addPiece) mempty

mapPW :: (Ord r, QAlg r) => (Piece r -> Piece r) -> Piecewise r -> Piecewise r
mapPW f = pw . map f . pieces

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

cdfPiece :: (Ord r, QAlg r) => Piece r -> r -> r
cdfPiece x@(Piece a b p) =
    let m = intPiece x
    in  \t -> case t of
            _
                | t <= a    -> 0
                | t >= b    -> m
                | otherwise -> defint a t p

beforePiece :: (Eq r, QAlg r) => r -> r -> Polynomial r () -> Polynomial r () -> Piece r
beforePiece a b p q =
    Piece a b $ p * defint (var ()) (constant b) (mapCoeff constant q)

revTimePiece :: (Eq r, Num r) => Piece r -> Piece r
revTimePiece (Piece a b p) = Piece (-b) (-a) $ subst p $ const $ - var ()

residualPiece :: forall r. (Ord r, QAlg r)
           => r
           -> r
           -> Polynomial r ()
           -> Polynomial r ()
           -> Piece r
residualPiece a b p q = Piece
    0
    (b - a)
    (defint (constant a)
            (constant b - var ())
            (p' * q'))
  where
    p', q' :: Polynomial (Polynomial r ()) ()
    p' = mapCoeff constant p
    q' = free (constant . constant) (const $ var () + constant (var ())) q

residualPiece' :: forall r. (Ord r, QAlg r)
            => Piece r
            -> Piece r
            -> Piecewise r
residualPiece' (Piece a b p) (Piece c d q)
    | c - a <= d - b = pw [ Piece (c - b) (c - a) $ f (c' - x) b'
                          , Piece (c - a) (d - b) $ f a' b'
                          , Piece (d - b) (d - a) $ f a' (d' - x)
                          ]
    | otherwise      = pw [ Piece (c - b) (d - b) $ f (c' - x) b'
                          , Piece (d - b) (c - a) $ f (c' - x) (d' - x)
                          , Piece (c - a) (d - a) $ f a' (d' - x)
                          ]
  where
    p', q' :: Polynomial (Polynomial r ()) ()
    p' = mapCoeff constant p
    q' = free (constant . constant) (const $ var () + constant (var ())) q

    a', b', c', d', x :: Polynomial r ()
    a' = constant a
    b' = constant b
    c' = constant c
    d' = constant d
    x  = var ()

    f :: Polynomial r () -> Polynomial r () -> Polynomial r ()
    f l u = defint l u (p' * q')

scalePiece :: (Eq r, Num r) => r -> Piece r -> Piece r
scalePiece r (Piece a b p) = Piece a b $ constant r * p

shiftPiece :: (Eq r, Num r) => r -> Piece r -> Piece r
shiftPiece r (Piece a b p) = Piece (a + r) (b + r) $ subst p $ const $ var () - constant r

uniformPW :: (Ord r, Fractional r, QAlg r) => r -> r -> Piecewise r
uniformPW a b = pw [Piece a b $ constant (1 / (b - a))]

free :: (Eq s, Num s) => (r -> s) -> (v -> s) -> Polynomial r v -> s
free f g p = eval g $ mapCoeff f p

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
