{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}

module Ouroboros.Chi_Calculus.Process.DeltaQ (

    --deltaQ

) where

import Prelude                                      hiding (map)

import Control.Monad                                (void)

import Data.Function                                (fix)
import Data.Functor.Const                           (Const (Const, getConst))
import Data.Functor.Identity                        (Identity (Identity, runIdentity))
import Data.List.FixedLength                        (map)

import Numeric.Natural                              (Natural)

import Ouroboros.Chi_Calculus.Data                  as Data
import Ouroboros.Chi_Calculus.Process               (Interpretation,
                                                     Process (..))
import Ouroboros.Chi_Calculus.Process.DeltaQ.DeltaQ (DeltaQ)
