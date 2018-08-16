module Ouroboros.Chi_Calculus.Interpretation.Exec (

    exec

) where

import Prelude hiding (map)

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (MVar, putMVar, takeMVar, newEmptyMVar)

import Data.Function (fix)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.List.FixedLength (map)

import Ouroboros.Chi_Calculus (Process (..))
import Ouroboros.Chi_Calculus.Interpretation (Interpretation)

exec :: Interpretation Identity MVar (IO ())
exec Stop                 = return ()
exec (Send chan val)      = putMVar chan (runIdentity val)
exec (Receive chan cont)  = takeMVar chan >>= exec . cont . Identity
exec (Parallel prc1 prc2) = forkIO (exec prc1) >>
                            forkIO (exec prc2) >>
                            return ()
exec (NewChannel cont)    = newEmptyMVar >>= exec . cont
exec (Var meaning)        = meaning
exec (Letrec defs res)    = exec (res (fix (map exec . defs)))
