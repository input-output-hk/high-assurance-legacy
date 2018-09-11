import Control.Concurrent (threadDelay)
import Control.Monad (forever)

import Ouroboros.ChiCalculus.Examples.DiningPhilosophers (
           runWithLogger,
           diningPhilosophers,
           defaultPhilosophers
       )

main :: IO ()
main = runWithLogger (diningPhilosophers defaultPhilosophers) >>
       forever (threadDelay maxBound)
