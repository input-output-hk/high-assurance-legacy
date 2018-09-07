{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Ouroboros.ChiCalculus.Process (

    Process (Stop, Guard, (:<:), (:>:), (:|:), NewChannel, Letrec, PVar),
    Channel,
    ClosedProcess,
    Interpretation,
    interpret,
    parallel,
    newChannels,
    plet,
    pfix,
    (<#)

) where

import Control.Concurrent.MVar (MVar)
import Control.Monad (replicateM)
import Control.Monad.Trans.Cont (cont, runCont)

import Data.List.FixedLength (List, singleton, fromSingleton)
import Data.Type.Natural (TypeNatural)

import           Ouroboros.ChiCalculus.Data (VarData (dvar))
import qualified Ouroboros.ChiCalculus.Data as Data (Interpretation)

infixr 3 :<:
infixr 3 :>:
infixr 2 :|:
infix  3 <#

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

type Channel = MVar

type ClosedProcess dat = forall d p . Process dat d p

type Interpretation d p = forall dat .
                          Data.Interpretation dat d -> Process dat d p -> p

interpret :: Interpretation d p
          -> Data.Interpretation dat d
          -> ClosedProcess dat
          -> p
interpret inter = inter

parallel :: [Process dat d p] -> Process dat d p
parallel = foldr (:|:) Stop

newChannels :: Int -> ([d (Channel a)] -> Process dat d p) -> Process dat d p
newChannels count = runCont $ replicateM count $ cont NewChannel

plet :: Process dat d p -> (p -> Process dat d p) -> Process dat d p
plet prc fun = Letrec (const (singleton prc)) (fun . fromSingleton)

pfix :: (p -> Process dat d p) -> Process dat d p
pfix fun = Letrec (singleton . fun . fromSingleton) (PVar . fromSingleton)

(<#) :: VarData dat
     => dat d (Channel m)
     -> (dat d (Channel a) -> dat d m)
     -> (d a -> Process dat d p)
     -> Process dat d p
(obj <# msg) cont = NewChannel $ \ resp ->
                    obj :<: msg (dvar resp) :|: dvar resp :>: cont
