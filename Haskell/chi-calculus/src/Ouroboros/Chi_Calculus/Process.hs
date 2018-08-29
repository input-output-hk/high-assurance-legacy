{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.Chi_Calculus.Process (

    Process (Stop, Guard, (:<:), (:>:), (:|:), NewChannel, Var, Letrec),
    Interpretation,
    interpret

) where

import Data.List.FixedLength (List)
import Data.Type.Natural (TypeNatural)

import qualified Ouroboros.Chi_Calculus.Data as Data (Interpretation)

{-|
    Processes of the χ-calculus with support for @letrec@ constructions. This
    definition uses parametric higher-order abstract syntax (PHOAS).
-}
data Process dat c d p where

    Stop       :: Process dat c d p

    Guard      :: dat d Bool
               -> Process dat c d p
               -> Process dat c d p

    (:<:)      :: c a
               -> dat d a
               -> Process dat c d p

    (:>:)      :: c a
               -> (d a -> Process dat c d p)
               -> Process dat c d p

    (:|:)      :: Process dat c d p
               -> Process dat c d p
               -> Process dat c d p

    NewChannel :: (c a -> Process dat c d p)
               -> Process dat c d p

    Var        :: p
               -> Process dat c d p

    Letrec     :: TypeNatural n
               => (List n p -> List n (Process dat c d p))
               -> (List n p -> Process dat c d p)
               -> Process dat c d p

type ClosedProcess dat = forall c d p . Process dat c d p

type Interpretation c d p = forall dat .
                            Data.Interpretation dat d -> Process dat c d p -> p

interpret :: Interpretation c d p
          -> Data.Interpretation dat d
          -> ClosedProcess dat
          -> p
interpret inter = inter
