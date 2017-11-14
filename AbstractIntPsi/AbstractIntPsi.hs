{-------------------------------------------------------------------------------
  Prototype development: PHOAS representation of the psi calculus with various
  interpreters: execution, pretty-printing, and abstract interpretation using
  a simple cost model domain.
-------------------------------------------------------------------------------}

{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

module Main (main, Cost(..)) where

import Prelude hiding (max)
import Control.Exception
import Control.Monad.State (State, state, evalState)
import Data.Function (fix)
import Data.Functor.Const
import Data.Functor.Identity
import Data.IORef
import Data.List (foldl')
import Data.Map.Strict (Map)
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.String
import GHC.Generics (Generic)
import Text.Show.Pretty (PrettyVal(..), dumpStr)
import qualified Prelude
import qualified Data.Map.Strict  as Map
import qualified Data.Set         as Set

{-------------------------------------------------------------------------------
  Simplified embedding of the psi calculus, parameterized by

  * interpretation functor |f| over values
  * interpretation functor |g| over processes
-------------------------------------------------------------------------------}

type family Chan (g :: * -> *) :: * -> *

data Psi f g where
  Done :: Psi f g
  Int  :: g (Psi f g) -> Psi f g
  In   :: Chan g a -> (f a -> Psi f g) -> Psi f g
  Out  :: Chan g a -> f a -> Psi f g -> Psi f g

{-------------------------------------------------------------------------------
  Simple examples

  As long as process definitions are entirely polymorphic in the functors,
  they can only denote terms in the bare abstract syntax.
-------------------------------------------------------------------------------}

simple :: Chan g a -> Chan g a -> Psi f g
simple i o = In i $ \a -> In i $ \a' -> Out o a' $ Out o a $ Done

{-------------------------------------------------------------------------------
  Interpretation
-------------------------------------------------------------------------------}

-- | General form of an interpreter
type Interpreter f g = Psi f g -> g (Psi f g)

class Interpret f g | g -> f where
  int :: Interpreter f g

{-------------------------------------------------------------------------------
  Running

  The model we use for computation does not match the psi calculus, as it
  doesn't implement synchronous communication. That doesn't matter much for the
  current demonstration however.
-------------------------------------------------------------------------------}

newtype Execute a = Execute { execute :: IO () }

type instance Chan Execute = Queue

instance Interpret Identity Execute where
  int = Execute . go
    where
      go :: Psi Identity Execute -> IO ()
      go Done        = return ()
      go (Int x)     = execute x
      go (In  c   k) = do a <- dequeue c ; go $ k (Identity a)
      go (Out c a k) = do enqueue c (runIdentity a) ; go k

execute' :: Psi Identity Execute -> IO ()
execute' = execute . int

{-------------------------------------------------------------------------------
  Pretty-printing domain

  The pretty-printer generates a string; it uses a state monad to generate
  fresh variable names.
-------------------------------------------------------------------------------}

newtype Pretty a = Pretty { pretty :: State Int String }

instance IsString (Pretty a) where
  fromString = Pretty . return

(<>) :: Pretty a -> Pretty b -> Pretty c
Pretty a <> Pretty b = Pretty $ (++) <$> a <*> b

scope :: String -> (Pretty b -> Pretty a) -> Pretty a
scope prefix f = Pretty $ do
    x <- state $ \n -> (Pretty (return (prefix ++ show n)), n + 1)
    pretty (f x)

{-------------------------------------------------------------------------------
  Pretty-printer proper
-------------------------------------------------------------------------------}

type instance Chan Pretty = Pretty

instance Interpret Pretty Pretty where
  int = go
    where
      go :: Psi Pretty Pretty -> Pretty (Psi Pretty Pretty)
      go Done        = "done"
      go (Int r)     = r
      go (Out c a k) = "output " <> c <> " " <> a <> " $ " <> go k
      go (In  c   k) = scope "x" $ \x -> "input " <> c <> " $ \\" <> x <> " -> " <> go (k x)

pretty' :: Psi Pretty Pretty -> String
pretty' = (`evalState` 0) . pretty . int

{-------------------------------------------------------------------------------
  Cost analysis domain

  We just count the number of inputs and outputs that a process is doing,
  with support for unknown values to deal with recursion.
-------------------------------------------------------------------------------}

data Count = Upper Int | Unknown
  deriving (Show, Generic, PrettyVal)

data Cost =
    Cost {
        costIn  :: Count
      , costOut :: Count
      }
  deriving (Show, Generic, PrettyVal)

-- | Conditional cost
--
-- Note: |Conditional a| is a map from "conditions" to |a|
type CondCost = Conditional Cost

instance MaxPlus Count where
  zero = Upper 0

  Upper n `plus` Upper m = Upper (n `plus` m)
  _       `plus` _       = Unknown

  Upper n `max` Upper m = Upper (n `max` m)
  _       `max` _       = Unknown


instance MaxPlus Cost where
  zero = Cost zero zero

  Cost i o `plus` Cost i' o' = Cost (i `plus` i') (o `plus` o')
  Cost i o `max`  Cost i' o' = Cost (i `max`  i') (o `max`  o')

unknownCost :: CondCost
unknownCost = unconditional (Cost Unknown Unknown)

{-------------------------------------------------------------------------------
  Cost analysis proper
-------------------------------------------------------------------------------}

data Probability = Prob Double | UnknownProb

data AbsValue a where
    -- | Any unknown value
    UnknownValue :: AbsValue a

    -- | Condition with a certain probability
    Condition :: Condition -> Probability -> AbsValue a

newtype AbsProc a = AbsProc { absProc :: CondCost }

type instance Chan AbsProc = Const ()

instance Interpret AbsValue AbsProc where
  int = AbsProc . go
    where
      go :: Psi AbsValue AbsProc -> CondCost
      go Done        = zero
      go (Int r)     = absProc r
      go (In _    k) = unconditional (Cost (Upper 1) (Upper 0)) `plus` go (k UnknownValue)
      go (Out _ _ k) = unconditional (Cost (Upper 0) (Upper 1)) `plus` go k

absProc' :: Psi AbsValue AbsProc -> CondCost
absProc' = absProc . int

{-------------------------------------------------------------------------------
  Ad-hoc polymorphism

  We can introduce constraints on the interpretation of values or the
  interpretation of processes in order to define more interesting processes.
  Whenever we do this, we have to show that the various interpretation domains
  we use can all support these new operations.

  For example, we may wish to tests values if they are even.
-------------------------------------------------------------------------------}

class IsEven f where
  isEven :: Integral a => f a -> f Bool

instance IsEven Identity where
  isEven (Identity n) = Identity (n `mod` 2 == 0)

instance IsEven Pretty where
  isEven (Pretty x) = Pretty $ ("isEven " ++) <$> x

-- | Note that for the cost modelling we forget _which_ value we test, and
-- merely remember the test itself. This is an intentional simplification to
-- keep the cost analysis tractable.
instance IsEven AbsValue where
  isEven _ = Condition "IsEven" UnknownProb

{-------------------------------------------------------------------------------
  We may wish to introduce conditionals.
-------------------------------------------------------------------------------}

class Interpret f g => Choice f g where
  choice :: f Bool -> g a -> g a -> g a

choice' :: Choice f g => f Bool -> Psi f g -> Psi f g -> Psi f g
choice' b t f = Int (choice b (int t) (int f))

instance Interpret Identity g => Choice Identity g where
  choice (Identity b) t f = if b then t else f

instance Choice Pretty Pretty where
  choice b t f = "if " <> b <> " then " <> t <> " else " <> f

-- | We could instead (or additionally) do something with the probability here
instance Choice AbsValue AbsProc where
  choice UnknownValue    (AbsProc t) (AbsProc f) = AbsProc (max t f)
  choice (Condition c _) (AbsProc t) (AbsProc f) = AbsProc (conditional c t f)

{-------------------------------------------------------------------------------
  We can also introduce recursion in this manner
-------------------------------------------------------------------------------}

class Interpret f g => Recurse f g where
  recurse :: (g a -> g a) -> g a

recurse' :: Recurse f g => (Psi f g -> Psi f g) -> Psi f g
recurse' f = Int $ recurse (int . f . Int)

instance Recurse Identity Execute where
  recurse = fix

instance Recurse Pretty Pretty where
  recurse f = scope "r" $ \r -> "rec $ \\" <> r <> " -> " <> f r

-- | For the cost modelling, we specify an unknown cost for any recursive
-- occurrences of the process. This boils down to unrolling the process once.
instance Recurse AbsValue AbsProc where
  recurse f = f (AbsProc unknownCost)

{-------------------------------------------------------------------------------
  Example process with more interesting internal structure
-------------------------------------------------------------------------------}

echoOdd :: (IsEven f, Recurse f g, Choice f g) => Chan g Int -> Chan g Int -> Psi f g
echoOdd i o = recurse' $ \r -> In i $ \x -> choice' (isEven x) Done (Out o x $ r)

{-------------------------------------------------------------------------------
  Dealing with state

  In order to deal with state we introduce combinators to get and set the
  state, in similar way to the way we introduced combinators for choice and
  recursion.
-------------------------------------------------------------------------------}

class Interpret f g => HasState (s :: *) (f :: * -> *) (g :: * -> *) where
  getState :: (f s -> g a) -> g a
  updState :: (f s -> f s) -> g a -> g a

getState' :: HasState s f g => (f s -> Psi f g) -> Psi f g
getState' k = Int $ getState (int . k)

updState' :: HasState s f g => (f s -> f s) -> Psi f g -> Psi f g
updState' f k = Int $ updState f (int k)

{-------------------------------------------------------------------------------
  Running a stateful program

  We cannot give an instance of 'HasState' for 'Identity/Execute' because
  we need access to the state; so we define a new interpretation. A pure
  interpretation should also be possible (exercise for the reader :-).
-------------------------------------------------------------------------------}

newtype Stateful s a = Stateful { stateful :: IORef s -> IO () }

stateful' :: s -> Psi Identity (Stateful s) -> IO ()
stateful' s p = f =<< newIORef s
  where
    Stateful f = int p

type instance Chan (Stateful s) = Queue

{-------------------------------------------------------------------------------
  We then have to show that 'Stateful' satisfies the type classes we define
  above, as well as our new 'HasState' type class.
-------------------------------------------------------------------------------}

instance Interpret Identity (Stateful s) where
  int = Stateful . go
    where
      go :: Psi Identity (Stateful s) -> IORef s -> IO ()
      go Done        _ = return ()
      go (Int f)     r = stateful f r
      go (In c k)    r = do a <- dequeue c ; go (k (Identity a)) r
      go (Out c a k) r = do enqueue c (runIdentity a) ; go k r

instance Recurse Identity (Stateful s) where
  recurse = fix

instance HasState s Identity (Stateful s) where
  getState   k = Stateful $ \r -> do
                   s <- readIORef r
                   stateful (k (Identity s)) r
  updState f k = Stateful $ \r -> do
                   s <- readIORef r
                   writeIORef r (runIdentity . f . Identity $ s)
                   stateful k r

{-------------------------------------------------------------------------------
  Finally, we need to extend the pretty-printer and the abstract interpreter
  to deal with state. The pretty-printer is straight-forwarded; for the
  abstract interpretation we simply regard the state as an unknown value.
-------------------------------------------------------------------------------}

instance HasState s Pretty Pretty where
  getState   k = scope "s" $ \s -> "getState $ \\" <> s <> " -> " <> k s
  updState f k = "updState (\\s -> " <> f "s" <> "). " <> k

instance HasState s AbsValue AbsProc where
  getState   k = k UnknownValue
  updState _ k = k

{-------------------------------------------------------------------------------
  Example using state

  As an example program that deals with state we write a program that waits
  to receive an even number, but only tries a certain maximum number of times.
  The cost model we obtain here is

  > CondCost
  > { conds = [ IsEven , ReachedLimit ]
  > , costs =
  >     [ ( [ ( IsEven , False ) , ( ReachedLimit , False ) ]
  >       , Cost { costIn = Unknown , costOut = Unknown }
  >       )
  >     , ( [ ( IsEven , False ) , ( ReachedLimit , True ) ]
  >       , Cost { costIn = Upper 0 , costOut = Upper 0 }
  >       )
  >     , ( [ ( IsEven , True ) , ( ReachedLimit , False ) ]
  >       , Cost { costIn = Upper 1 , costOut = Upper 1 }
  >       )
  >     , ( [ ( IsEven , True ) , ( ReachedLimit , True ) ]
  >       , Cost { costIn = Upper 0 , costOut = Upper 0 }
  >       )
  >     ]
  > }
-------------------------------------------------------------------------------}

class ReachedLimit s f | f -> s where
  reachedLimit :: f s -> f Bool
  tick :: f s -> f s

instance ReachedLimit Int Identity where
  reachedLimit = fmap (== 0)
  tick         = fmap (\x -> x - 1)

instance ReachedLimit Int Pretty where
  reachedLimit l = "reachedLimit " <> l
  tick s = "tick " <> s

instance ReachedLimit Int AbsValue where
  reachedLimit _ = Condition "ReachedLimit" (Prob 0.2)
  tick = id

tryGetEven :: (HasState s f g, ReachedLimit s f, Choice f g, IsEven f, Recurse f g)
           => Chan g Int -> Chan g Int -> Psi f g
tryGetEven i o = recurse' $ \r ->
    getState' $ \s ->
    choice' (reachedLimit s)
      Done
      (In i $ \a ->
       choice' (isEven a)
         (Out o a $ Done)
         (updState' tick $ r))

{-------------------------------------------------------------------------------
  Guarded recursion

  Low-level primitives are good for language design (we need to provide fewer
  primitives to the program author if they can compose low-level primitives
  to build high level primitives) but less good for analysis.

  A good example is given by "bounded recursion", such as

  > rec $ \r0 ->
  >   getState $ \s1 ->
  >   if reachedLimit s1
  >     then done
  >     else input i $ \x2 ->
  >          if isEven x2
  >            then output o x2 $ done
  >            else updState (\s -> tick s). r0

  For general recursion we cannot do a very satisfactory cost analysis;
  however, if we provide an explicit construct for this kind of
  recursion-bounded-by-some-condition, we can do better, as we can make an
  informed guess how often the loop will be executed, and moreover we have
  an explicit base case.
-------------------------------------------------------------------------------}

class HasState s f g => BoundedRec s f g where
  boundedRec :: (f s -> f Bool) -> (g a -> g a) -> g a -> g a

boundedRec' :: BoundedRec s f g
            => (f s -> f Bool) -> (Psi f g -> Psi f g) -> Psi f g -> Psi f g
boundedRec' guard body k = Int $ boundedRec guard (int . body . Int) (int k)

{-------------------------------------------------------------------------------
  Of course we then have the usual instances for execution and pretty-printing
-------------------------------------------------------------------------------}

instance BoundedRec s Identity (Stateful s) where
  boundedRec guard body k = go
    where
      go = Stateful $ \r -> do
        b <- (runIdentity . guard . Identity) <$> readIORef r
        if b then stateful (body go) r
             else stateful k r

instance BoundedRec s Pretty Pretty where
  boundedRec guard body k = scope "r" $ \r -> scope "s" $ \s ->
       "rec $ \\" <> r <> " -> "
    <> "getState $ \\" <> s <> " -> "
    <> "if " <> guard s <> " then " <> k <> " else " <> body r

{-------------------------------------------------------------------------------
  The interesting instance is the one for cost analysis, where we compute
  how often the loop is executed on average (provided we have a known
  probability).
-------------------------------------------------------------------------------}

-- | Average number of iterations an "until" loop will execute, given
-- the probability that the guard evaluates to true.
avgNumIters :: Double -> Int
avgNumIters p = round ((1 - p) / p)

instance BoundedRec s AbsValue AbsProc where
  boundedRec :: forall a.
                (AbsValue s -> AbsValue Bool)
             -> (AbsProc a -> AbsProc a)
             -> AbsProc a
             -> AbsProc a
  boundedRec guard body k =
      case guard UnknownValue of
        Condition _ (Prob p) -> go (avgNumIters p)
        _otherwise           -> AbsProc unknownCost
    where
      go :: Int -> AbsProc a
      go 0 = k
      go n = body (go (n - 1))

{-------------------------------------------------------------------------------
  The look-for-even-numbers example rewritten; we obtain the cost model

  > CondCost
  > { conds = [ IsEven ]
  > , costs =
  >     [ ( [ ( IsEven , False ) ]
  >       , Cost { costIn = Upper 4 , costOut = Upper 0 }
  >       )
  >     , ( [ ( IsEven , True ) ]
  >       , Cost { costIn = Upper 1 , costOut = Upper 1 }
  >       )
  >     ]
  > }
-------------------------------------------------------------------------------}

tryGetEven' :: (BoundedRec s f g, ReachedLimit s f, Choice f g, IsEven f)
            => Chan g Int -> Chan g Int -> Psi f g
tryGetEven' i o = boundedRec'
                    reachedLimit
                    (\r -> In i $ \a ->
                        choice' (isEven a)
                        (Out o a $ Done)
                        (updState' tick $ r)
                      )
                    Done

{-------------------------------------------------------------------------------
  Testing
-------------------------------------------------------------------------------}

main :: IO ()
main = do
    putStrLn "* simple"
    putStrLn $ pretty' $ simple "i" "o"
    bracket (newQueue "i" [True, False]) printQueue $ \i ->
      bracket (newQueue "o" []) printQueue $ \o ->
        execute' $ simple i o
    putStrLn . dumpStr $ absProc' $ simple (Const ()) (Const ())

    putStrLn "* echoOdd"
    putStrLn $ pretty' $ echoOdd "i" "o"
    bracket (newQueue "i" [1,3,5,6,7,8]) printQueue $ \i ->
      bracket (newQueue "o" []) printQueue $ \o ->
        execute' $ echoOdd i o
    putStrLn . dumpStr $ absProc' $ echoOdd (Const ()) (Const ())

    putStrLn "* Running \"pure\" processes using withState"
    bracket (newQueue "i" [True, False]) printQueue $ \i ->
      bracket (newQueue "o" []) printQueue $ \o ->
        stateful' () $ simple i o

    putStrLn "* Stateful processes"
    putStrLn $ pretty' $ tryGetEven "i" "o"
    bracket (newQueue "i" [1,3,5,6,7,8]) printQueue $ \i ->
      bracket (newQueue "o" []) printQueue $ \o ->
        stateful' (5 :: Int) $ tryGetEven i o
    bracket (newQueue "i" [1,3,5,6,7,8]) printQueue $ \i ->
      bracket (newQueue "o" []) printQueue $ \o ->
        stateful' (2 :: Int) $ tryGetEven i o
    putStrLn . dumpStr $ absProc' $ tryGetEven (Const ()) (Const ())

    putStrLn "* Guarded recursion"
    putStrLn $ pretty' $ tryGetEven' "i" "o"
    bracket (newQueue "i" [1,3,5,6,7,8]) printQueue $ \i ->
      bracket (newQueue "o" []) printQueue $ \o ->
        stateful' (5 :: Int) $ tryGetEven' i o
    bracket (newQueue "i" [1,3,5,6,7,8]) printQueue $ \i ->
      bracket (newQueue "o" []) printQueue $ \o ->
        stateful' (2 :: Int) $ tryGetEven' i o
    putStrLn . dumpStr $ absProc' $ tryGetEven' (Const ()) (Const ())

    putStrLn "* OK"

{-------------------------------------------------------------------------------
  Auxiliary: very simple queue
-------------------------------------------------------------------------------}

type QueueId = String
data Queue a = Queue QueueId (IORef [a])

enqueue :: Queue a -> a -> IO ()
enqueue (Queue _ q) a = modifyIORef q (++ [a])

dequeue :: Queue a -> IO a
dequeue (Queue _ q) = atomicModifyIORef q (\(a:as) -> (as, a))

newQueue :: String -> [a] -> IO (Queue a)
newQueue n as = Queue n <$> newIORef as

printQueue :: Show a => Queue a -> IO ()
printQueue (Queue n q) = do as <- readIORef q ; putStrLn $ n ++ ": " ++ show as

{-------------------------------------------------------------------------------
  Miscellaneous
-------------------------------------------------------------------------------}

class MaxPlus a where
  zero :: a
  max  :: a -> a -> a
  plus :: a -> a -> a

instance MaxPlus Int where
  zero = 0
  max  = Prelude.max
  plus = (+)

repeatedly :: (a -> b -> b) -> ([a] -> b -> b)
repeatedly = flip . foldl' . flip

instance (PrettyVal k, PrettyVal a) => PrettyVal (Map k a) where
  prettyVal = prettyVal . Map.toList

instance PrettyVal a => PrettyVal (Set a) where
  prettyVal = prettyVal . Set.toList

{-------------------------------------------------------------------------------
  Auxiliary: conditional values
-------------------------------------------------------------------------------}

type Condition = String

-- | A decision for a set of conditions is function assigning every condition
-- to either True or False
type Decision = [(Condition, Bool)]

-- | Construct the set of all possible decisions for a set of conditions
allDecisions :: Set Condition -> [Decision]
allDecisions cs = sequence [[(c, b) | b <- [True, False]] | c <- Set.toList cs]

-- | Remove a condition from a decision
ignoring :: Decision -> Condition -> Decision
ignoring d c = filter ((/= c) . fst) d

-- | Conditional cost
--
-- Current representation is designed to be "obviously correct". Smarter
-- representations are probably possible.
data Conditional a = Conditional {
      -- | The set of decisions we consider
      conds :: Set Condition

      -- | Conditional cost
      --
      -- Invariant:
      --
      -- > Map.keys costs == Set.fromList (allDecisions conditions)
    , values :: Map Decision a
    }
  deriving (Show, Generic, PrettyVal)

-- | Unconditional cost
unconditional :: a -> Conditional a
unconditional a = Conditional Set.empty (Map.singleton [] a)

-- | Conditional cost
conditional :: Condition -> Conditional a -> Conditional a -> Conditional a
conditional c = merge [c] $ \d t f -> if fromJust (lookup c d) then t else f

merge :: [Condition]               -- ^ Additional conditions to add
      -> (Decision -> a -> a -> a) -- ^ Combining function
      -> Conditional a -> Conditional a -> Conditional a
merge cs f a b = Conditional conds' values'
  where
    conds'  = Set.unions [Set.fromList cs, conds a, conds b]
    a'      = addConditions (Set.toList conds') a
    b'      = addConditions (Set.toList conds') b
    values' = Map.fromList [
                 (d, f d (values a' Map.! d) (values b' Map.! d))
               | d <- allDecisions conds'
               ]

-- | Add a condition to an existing conditional cost (if not already there)
addCondition :: Condition -> Conditional a -> Conditional a
addCondition c cc | c `elem` conds cc = cc
addCondition c Conditional{..} = Conditional conds' values'
  where
    conds'  = Set.insert c conds
    values' = Map.fromList [
                 (d, values Map.! (d `ignoring` c))
               | d <- allDecisions conds'
               ]

addConditions :: [Condition] -> Conditional a -> Conditional a
addConditions = repeatedly addCondition

instance MaxPlus a => MaxPlus (Conditional a) where
  zero = unconditional zero
  max  = merge [] (const max)
  plus = merge [] (const plus)