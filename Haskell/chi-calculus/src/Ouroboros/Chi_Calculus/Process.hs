{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Ouroboros.Chi_Calculus.Process (

    Process (Stop, (:<:), (:>:), (:|:), NewChannel, Guard, Var, Letrec),
    ClosedProcess,
    closedProcess,
    Interpretation,
    interpret,
    InterpretationEnv,
    interpretEnv

) where

import           Data.List.FixedLength              (List)
import           Data.Type.Natural                  (TypeNatural)

import qualified Ouroboros.Chi_Calculus.Data        as Data (Interpretation)
import           Ouroboros.Chi_Calculus.Environment (Env, Env', ToFromEnv (..),
                                                     mapEnv')

{-|
    Processes of the χ-calculus with support for @letrec@ constructions. This
    definition uses parametric higher-order abstract syntax (PHOAS).
-}
data Process (dat :: (* -> *) -> (* -> *))
             (c   :: * -> *)
             (d   :: * -> *)
             (p   :: [*] -> *) :: * where

    Stop       :: Process dat c d p

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

    Guard      :: dat d Bool
               -> Process dat c d p
               -> Process dat c d p

    Var        :: p '[]
               -> Process dat c d p

    Letrec     :: TypeNatural n
               => (List n (p '[]) -> List n (Process dat c d p))
               -> (List n (p '[]) -> Process dat c d p)
               -> Process dat c d p

type ClosedProcess dat xs = forall c d p. Env' (Process dat c d p) c xs

closedProcess :: forall dat xs .
                 ToFromEnv xs
              => (forall c d p. Env (Process dat c d p) c xs)
              -> ClosedProcess dat xs
closedProcess env = fromEnv $ env @c @d @p :: forall c d p. Env' (Process dat c d p) c xs

type Interpretation c d p =  forall dat xs.
                             Data.Interpretation dat d
                          -> Env' (Process dat c d p) c xs
                          -> p xs

interpret :: Interpretation c d p
          -> Data.Interpretation dat d
          -> ClosedProcess dat xs
          -> p xs
interpret inter interDat = inter interDat

type InterpretationEnv c d p =  forall dat.
                                Data.Interpretation dat d
                             -> Process dat c d (Env' p c)
                             -> p

interpretEnv :: ToFromEnv xs
             => InterpretationEnv c d p
             -> Data.Interpretation dat d
             -> ClosedProcess dat xs
             -> Env p c xs
interpretEnv inter interDat = toEnv . mapEnv' (inter interDat)
