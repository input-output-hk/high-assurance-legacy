{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Psi.IO
Description : interpretation of @Psi@ in @IO@.
Copyright   : (c) Lars Brünjes, 2017
License     : MIT
Maintainer  : lars.bruenjes@iohk.io
Stability   : experimental
Portability : portable

This module defines an interpretation of @'Psi'@ in @'IO'@.
-}

module Psi.IO
    ( PsiIO (..)
    ) where

import Control.Concurrent      (forkIO, threadDelay)
import Control.Concurrent.MVar
import Control.Monad.Random    (MonadRandom (..))
import Data.Functor.Identity
import Distribution
import Probability
import Psi.Core

-- | A simple wrapper around @'IO'@-actions (of type @'IO' ()@).
newtype PsiIO a = PsiIO {runPsiIO :: IO ()}

instance Show a => Psi (PsiIO a) where

    type Chan (PsiIO a)        = MVar
    type Value (PsiIO a)       = Identity
    type Observation (PsiIO a) = a

    done         = PsiIO $ return ()
    nu k         = PsiIO $ newEmptyMVar >>= runPsiIO . k
    inp c k      = PsiIO $ takeMVar c >>= \b -> runPsiIO (k $ Identity b)
    out c v p    = PsiIO $ putMVar c (runIdentity v) >> runPsiIO p
    fork p q     = PsiIO $ forkIO (runPsiIO p) >> runPsiIO q
    observe a p  = PsiIO $ print a >> runPsiIO p
    delay d p    = PsiIO $ do
        s <- sampleDist d
        threadDelay $ 1000000 * fromIntegral s
        runPsiIO p
    choice r p q = PsiIO $ do
        x <- getRandomR (0, 1)
        runPsiIO $ if x <= probToDouble r then p else q
