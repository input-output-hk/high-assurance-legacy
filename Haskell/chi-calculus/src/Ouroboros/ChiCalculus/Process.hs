{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.ChiCalculus.Process (

    Process (Stop, (:?:), (:<:), (:>:), (:|:), NewChannel, Letrec, PVar),
    ClosedProcess,
    Interpretation,
    interpret,
    parallel,
    newChannels,
    plet,
    pfix,
    (<#)

) where

import Control.Monad (replicateM)
import Control.Monad.Trans.Cont (cont, runCont)

import Data.List.FixedLength (List, singleton, fromSingleton)
import Data.Type.Natural (TypeNatural)

import           Ouroboros.ChiCalculus.Data (VarData (dvar))
import qualified Ouroboros.ChiCalculus.Data as Data (Interpretation)

infixr 3 :?:
infixr 3 :<:
infixr 3 :>:
infixr 2 :|:
infix  3 <#

{-|
    Processes of the χ-calculus with support for @letrec@ constructions. This
    definition uses parametric higher-order abstract syntax (PHOAS).
-}
data Process dat c d p where

    Stop       :: Process dat c d p

    (:?:)      :: dat c d Bool
               -> Process dat c d p
               -> Process dat c d p

    (:<:)      :: dat c d (c a)
               -> dat c d a
               -> Process dat c d p

    (:>:)      :: dat c d (c a)
               -> (d a -> Process dat c d p)
               -> Process dat c d p

    (:|:)      :: Process dat c d p
               -> Process dat c d p
               -> Process dat c d p

    NewChannel :: (d (c a) -> Process dat c d p)
               -> Process dat c d p

    Letrec     :: TypeNatural n
               => (List n p -> List n (Process dat c d p))
               -> (List n p -> Process dat c d p)
               -> Process dat c d p

    PVar       :: p
               -> Process dat c d p

type ClosedProcess dat = forall c d p . Process dat c d p

type Interpretation c d p
    = forall dat . Data.Interpretation dat c d -> Process dat c d p -> p

interpret :: Interpretation c d p
          -> Data.Interpretation dat c d
          -> ClosedProcess dat
          -> p
interpret inter = inter

parallel :: [Process dat c d p] -> Process dat c d p
parallel = foldr (:|:) Stop

newChannels :: Int -> ([d (c a)] -> Process dat c d p) -> Process dat c d p
newChannels count = runCont $ replicateM count $ cont NewChannel

plet :: Process dat c d p -> (p -> Process dat c d p) -> Process dat c d p
plet prc fun = Letrec (const (singleton prc)) (fun . fromSingleton)

pfix :: (p -> Process dat c d p) -> Process dat c d p
pfix fun = Letrec (singleton . fun . fromSingleton) (PVar . fromSingleton)

(<#) :: VarData dat
     => dat c d (c m)
     -> (dat c d (c a) -> dat c d m)
     -> (d a -> Process dat c d p)
     -> Process dat c d p
(obj <# msg) cnt = NewChannel $ \ resp ->
                   obj :<: msg (dvar resp) :|: dvar resp :>: cnt
