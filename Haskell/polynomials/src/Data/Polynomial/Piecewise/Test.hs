{-# LANGUAGE TemplateHaskell #-}

module Data.Polynomial.Piecewise.Test where

import Data.Function             (on)
import Data.Polynomial.Class
import Data.Polynomial.Piecewise
import Test.QuickCheck

--instance Arbitrary Rational where


data TPol r a =
      Iota r
    | Var a
    | Add (TPol r a) (TPol r a)
    | Mul (TPol r a) (TPol r a)

toPol :: (Eq r, Num r, Ord a) => TPol r a -> Polynomial r a
toPol (Iota r)  = constant r
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

toPiece :: (Eq r, Num r) => TPiece r -> Piece r
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

prop_pw_valid :: [TPiece Rational] -> Property
prop_pw_valid xs = let x = pw $ map toPiece xs
                   in counterexample (show x) $ pwValid x

prop_pw_value :: Rational -> [TPiece Rational] -> Property
prop_pw_value n xs =
    let ys       = map toPiece xs
        expected = sum [evalPiece n y | y <- ys]
        res      = pw ys
        actual   = evalPW n res
    in  all (\p -> n /= pBeg p && n /= pEnd p) ys
        ==> counterexample (show res) $ actual === expected

prop_pw_integral :: [TPiece Rational] -> Property
prop_pw_integral xs =
    let ys       = map toPiece xs
        expected = sum $ map intPiece ys
        actual   = mass $ pw ys
    in  actual === expected

prop_convolvePW_commutes :: [TPiece Rational] -> [TPiece Rational] -> Property
prop_convolvePW_commutes xs ys =
    let x = pw $ map toPiece xs
        y = pw $ map toPiece ys
    in  x `convolve` y === y `convolve` x

prop_convolvePW_integral :: [TPiece Rational] -> [TPiece Rational] -> Property
prop_convolvePW_integral xs ys =
    let x  = pw $ map toPiece xs
        y  = pw $ map toPiece ys
        ix = mass x
        iy = mass y
        iz = mass $ x `convolve` y
    in  counterexample (show (ix, iy)) $ iz === ix * iy

prop_beforePW_integral :: [TPiece Rational] -> [TPiece Rational] -> Property
prop_beforePW_integral xs ys =
    let x  = pw $ map toPiece xs
        y  = pw $ map toPiece ys
        xy = before x y
        yx = before y x
        ix = mass x
        iy = mass y
        iz = mass xy + mass yx
    in  counterexample (show (x, ix, y, iy, xy, yx)) $ iz === ix * iy

prop_ftfPW_commutes :: [TPiece Rational] -> [TPiece Rational] -> Property
prop_ftfPW_commutes xs ys =
    let x = pw $ map toPiece xs
        y = pw $ map toPiece ys
    in  x `ftf` y === y `ftf` x

prop_ftfPW_integral :: [TPiece Rational] -> [TPiece Rational] -> Property
prop_ftfPW_integral xs ys =
    let x  = pw $ map toPiece xs
        y  = pw $ map toPiece ys
        z  = x `ftf` y
        ix = mass x
        iy = mass y
        iz = mass z
    in  counterexample (show (x, ix, y, iy, z)) $ iz === ix * iy

prop_beforePW_deltaPW :: [TPiece Rational] -> [TPiece Rational] -> Property
prop_beforePW_deltaPW xs ys =
    let x  = pw $ map toPiece xs
        y  = pw $ map toPiece ys
        i  = mass $ before x y
        j  = mass $ residual x y
    in  i === j

return []
runTests :: IO Bool
runTests = $quickCheckAll

runVerboseTests :: IO Bool
runVerboseTests = $verboseCheckAll
