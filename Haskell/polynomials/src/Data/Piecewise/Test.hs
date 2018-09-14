module Data.Piecewise.Test where

import Data.Alg
import Data.Function   (on)
import Data.Piecewise
import Data.Pol
import Test.QuickCheck

data TPol r a =
      Iota r
    | Var a
    | Add (TPol r a) (TPol r a)
    | Mul (TPol r a) (TPol r a)

toPol :: Num r => TPol r a -> Pol r a
toPol (Iota r)  = iota r
toPol (Var a)   = var a
toPol (Add p q) = toPol p + toPol q
toPol (Mul p q) = toPol p * toPol q

instance (Num r, Eq r, Show r, Ord a, Show a) => Show (TPol r a) where
    show = show . toPol

instance (Num r, Eq r, Ord a) => Eq (TPol r a) where
    (==) = (==) `on` toPol

instance (Num r, Ord r, Ord a) => Ord (TPol r a) where
    compare = compare `on` toPol

instance (Arbitrary a, Arbitrary r, Eq r, Num r) => Arbitrary (TPol r a) where

    arbitrary = sized $ \s -> genDeg (min s 10)
      where
        genDeg 0 = Iota <$> arbitrary
        genDeg 1 = Var <$> arbitrary
        genDeg d = oneof [genAdd d, genMul d]

        genAdd d = do
            i <- choose (0, d - 1)
            x <- genMul d
            y <- genDeg i
            return $ Add x y

        genMul d = do
            i <- choose (1, d - 1)
            let j = d - i
            Mul <$> genDeg i <*> genDeg j

    shrink (Iota r)  = map Iota $ shrink r
    shrink (Var a)   = map Var $ shrink a
    shrink (Add p q) =  p
                     :  q
                     :  [Add p' q | p' <- shrink p]
                     ++ [Add p q' | q' <- shrink q]
    shrink (Mul p q) =  p
                     :  q
                     :  [Mul p' q | p' <- shrink p]
                     ++ [Mul p q' | q' <- shrink q]

data TPiece r = TPiece r r (TPol r ())
    deriving (Show, Eq, Ord)

toPiece :: Num r => TPiece r -> Piece r
toPiece (TPiece b e p) = Piece b e $ toPol p

instance (Eq r, Num r, Arbitrary r) => Arbitrary (TPiece r) where

    arbitrary = TPiece <$> arbitrary <*> arbitrary <*> arbitrary

    shrink (TPiece b e p) =  [TPiece b' e p | b' <- shrink b]
                          ++ [TPiece b e' p | e' <- shrink e]
                          ++ [TPiece b e p' | p' <- shrink p]

pwValid :: (Ord r, Num r) => Piecewise r -> Bool
pwValid = go . pieces
  where
    go []           = True
    go [x]          = pValid x
    go (x@(Piece _ e p) : y@(Piece b' _ p') : ps)
        =  pValid x
        && (e < b' || (e == b' && p /= p'))
        && go (y : ps)

    pValid (Piece b e p) = b < e && p /= 0

prop_pw_valid :: [TPiece Int] -> Property
prop_pw_valid xs = let x = pw $ map toPiece xs
                   in counterexample (show x) $ pwValid x

pieceValue :: (Num r, Ord r) => Piece r -> r -> r
pieceValue (Piece b e p) r
    | b == e           = 0
    | b >  e           = pieceValue (Piece e b $ -p) r
    | r <= b || r >= e = 0
    | otherwise        = eval (const r) p

prop_pw_value :: Int -> [TPiece Int] -> Property
prop_pw_value n xs =
    let ys       = map toPiece xs
        expected = sum [pieceValue y n | y <- ys]
        res      = pw ys
        actual   = sum [pieceValue y n | y <- pieces res]
    in  all (\p -> n /= pBeg p && n /= pEnd p) ys
        ==> counterexample (show res) $ actual === expected
