import Control.Concurrent (threadDelay)
import Control.Monad (forever)

import Ouroboros.ChiCalculus.Examples.Reverser (runWithStdIO, reverser)

main :: IO ()
main = runWithStdIO reverser >> forever (threadDelay maxBound)
