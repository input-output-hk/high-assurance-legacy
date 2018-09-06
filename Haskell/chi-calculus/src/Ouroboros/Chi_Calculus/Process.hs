{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.Chi_Calculus.Process (

    Process (Stop, Guard, (:<:), (:>:), (:|:), NewChannel, Letrec, PVar),
    Channel,
    ClosedProcess,
    Interpretation,
    interpret

) where

import Data.List.FixedLength (List)
import Data.Type.Natural (TypeNatural)

import qualified Ouroboros.Chi_Calculus.Data as Data (Interpretation)

infixr 3 :<:
infixr 3 :>:
infixr 2 :|:

{-|
    Processes of the χ-calculus with support for @letrec@ constructions. This
    definition uses parametric higher-order abstract syntax (PHOAS).
-}
data Process dat d p where

    Stop       :: Process dat d p

    Guard      :: dat d Bool
               -> Process dat d p
               -> Process dat d p

    (:<:)      :: dat d (Channel a)
               -> dat d a
               -> Process dat d p

    (:>:)      :: dat d (Channel a)
               -> (d a -> Process dat d p)
               -> Process dat d p

    (:|:)      :: Process dat d p
               -> Process dat d p
               -> Process dat d p

    NewChannel :: (d (Channel a) -> Process dat d p)
               -> Process dat d p

    Letrec     :: TypeNatural n
               => (List n p -> List n (Process dat d p))
               -> (List n p -> Process dat d p)
               -> Process dat d p

    PVar       :: p
               -> Process dat d p

data Channel a

type ClosedProcess dat = forall d p . Process dat d p

type Interpretation d p = forall dat .
                          Data.Interpretation dat d -> Process dat d p -> p

interpret :: Interpretation d p
          -> Data.Interpretation dat d
          -> ClosedProcess dat
          -> p
interpret inter = inter
