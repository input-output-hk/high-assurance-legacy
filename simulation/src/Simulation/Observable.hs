module Simulation.Observable
    ( Observable
    , observeDeltaQ
    ) where

import Data.Typeable
import DeltaQ.Core
import Simulation.Pure
import Simulation.Thread
import Simulation.Time
import Simulation.Utils

type Observable a = [(Seconds, a)] -> Maybe Seconds

observeDeltaQ :: Typeable a => Maybe Seconds -> Thread () -> Observable a -> DeltaQ
observeDeltaQ ms t obs = DeltaQ $ \g ->
    let (logs, g') = simulateFor ms g t
    in  (obs $ matches logs, g')
