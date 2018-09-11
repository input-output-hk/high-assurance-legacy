import           Charts
import           Control.Monad
import           Data.DeltaQ
import           Data.List       (intercalate)
import qualified Data.Map.Strict as M
import           Graph
import           Process
import           Text.Printf     (printf)

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
    let dq     = mix 0.5 never $ un 5 15
        (g, s) = graphFromList xs
        resEx  = measure g dq
    print resEx
    toFileDDQ s resEx

{-
    let proc = networkP dq g
        m    = runProbM $ toQueue proc
    forM_ (M.toList m) $ \(ys, p) -> do
        printf "p = %6.4f\n" (fromRational $ toRational $ getProb p :: Double)
        putStrLn ""
        forM_ ys $ \(dq', msg) -> do
            printf "%d: %s\n" (msgChan msg) (msgPayload msg)
            print dq'
            putStrLn ""
            -}

main :: IO ()
main = testGraph graphs

graphFromList :: [(Int, Int)] -> (Graph, String)
graphFromList xs =
    let n = maximum $ concatMap (\(x, y) -> [x, y]) xs
        g = (n, xs)
        s = "graph-" ++ intercalate "-" (map (\(x, y) -> show x ++ show y) xs) ++ ".png"
    in  (g, s)

type DQ = DDQ Double IntP

ex :: Int -> DQ
ex = exact . Finite . intP

un :: Int -> Int -> DQ
un a b = uniform (intP a) (intP b)
