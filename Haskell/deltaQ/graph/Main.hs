import Charts
import Data.DeltaQ
import Graph

testGraph :: Graph
testGraph = buildGraph $ do
    m <- addNode
    n <- addNode
    o <- addNode
    p <- addNode
    addEdge m n
    addEdge m o
    addEdge m p
    addEdge n o
    addEdge n p
    addEdge o p

testGraphIO :: IO ()
testGraphIO = do
    let dq  = mix 0.5 never $ un 5 10
        res = measure testGraph dq
    print res
    toFileDDQ "graph-12-13-14-23-24-34.png" res
  where
    un :: Int -> Int -> DQ
    un a b = uniform (intP a) (intP b)

main :: IO ()
main = testGraphIO
