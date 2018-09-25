import Data.DeltaQ
import Data.List   (intercalate)
import Graph

graphs :: [[(Int, Int)]]
graphs =
    [ [(1,2)]
    , [(1,2),(2,3)]
    , [(1,2),(2,3),(3,1)]
    , [(1,2),(2,3),(3,4)]
    , [(1,2),(2,3),(3,4),(4,1)]
    , [(1,2),(2,3),(3,4),(4,5)]
    , [(1,2),(2,3),(3,4),(4,5),(5,1)]
    , [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
    , [(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
    ]

testGraph :: [[(Int, Int)]] -> IO ()
testGraph = mapM_ $ \xs -> do
    print xs
    let dq     = mix 0.5 never $ uniformMixed 0.5 1.5
        (g, _) = graphFromList xs
    graphIO dq 10 g $ const (return ()) -- \res -> toFileMixed s (getMixed res)

main :: IO ()
main = testGraph graphs

graphFromList :: [(Int, Int)] -> (Graph, String)
graphFromList xs =
    let n = maximum $ concatMap (\(x, y) -> [x, y]) xs
        g = (n, xs)
        s = "graph-" ++ intercalate "-" (map (\(x, y) -> show x ++ show y) xs) ++ ".png"
    in  (g, s)

ex :: Int -> Mixed
ex = exact . Finite . fromIntegral

un :: Int -> Int -> Mixed
un a b = uniformMixed (fromIntegral a) (fromIntegral b)
