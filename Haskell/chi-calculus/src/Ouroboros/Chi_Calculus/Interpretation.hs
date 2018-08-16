module Ouroboros.Chi_Calculus.Interpretation (

    Interpretation,
    interpret

) where

import Ouroboros.Chi_Calculus (Process, ClosedProcess)

type Interpretation v c p = Process v c p -> p

interpret :: Interpretation v c p -> ClosedProcess v -> p
interpret interpretation = interpretation
