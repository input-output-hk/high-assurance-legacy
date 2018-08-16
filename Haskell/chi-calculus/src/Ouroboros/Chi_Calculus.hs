module Ouroboros.Chi_Calculus (

    Process (Stop, Send, Receive, Parallel, NewChannel, Var, Letrec),
    ClosedProcess

) where

import Data.List.FixedLength (List)
import Data.Type.Natural (TypeNatural)

{-|
    Processes of the χ-calculus with support for @letrec@ constructions. This
    definition uses parametric higher-order abstract syntax (PHOAS).
-}
data Process v c p where

    Stop       :: Process v c p

    Send       :: c a
               -> v a
               -> Process v c p

    Receive    :: c a
               -> (v a -> Process v c p)
               -> Process v c p

    Parallel   :: Process v c p
               -> Process v c p
               -> Process v c p

    NewChannel :: (c a -> Process v c p)
               -> Process v c p

    Var        :: p
               -> Process v c p

    Letrec     :: TypeNatural n
               => (List n p -> List n (Process v c p))
               -> (List n p -> Process v c p)
               -> Process v c p

type ClosedProcess v = forall c p . Process v c p
