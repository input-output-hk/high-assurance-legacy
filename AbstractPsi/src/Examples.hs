{-# LANGUAGE TypeFamilies #-}

module Examples
    ( pingPong
    , problem
    ) where

import Psi

pingPong :: Psi p => p
pingPong = nu $ \c ->
    fork
        (out c undefined $
         inp c $ const done)
        (inp c $ \v -> out c v done)

problem :: Psi p => p
problem = nu $ \c ->
    fork
        (fork
            (out c undefined done)
            (out c undefined done))
        (fork
            (inp c $ const done)
            (inp c $ const done))
