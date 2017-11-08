{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Simulation.Pure
    ( M
    , ThreadId'
    , Channel'
    , simulateFor
    , simulate
    ) where

import           Control.Monad.State
import           Control.Monad.Trans.Free
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as M
import           Data.Typeable
import           Simulation.Queue          (Queue)
import qualified Simulation.Queue          as Q
import           Simulation.Thread
import           Simulation.Time
import           Simulation.TimeQueue      (TimeQueue)
import qualified Simulation.TimeQueue      as T

newtype ThreadId' = ThreadId' Int deriving (Eq, Ord)

instance Show ThreadId' where
    show (ThreadId' n) = '#' : show n

newtype Channel' a = Channel' {channelId :: Int} deriving Show

data CHANNEL where
    CHANNEL :: Typeable a => Queue a -> CHANNEL

emptyCHANNEL :: forall a. Typeable a => Channel' a -> CHANNEL
emptyCHANNEL _ = CHANNEL (Q.empty :: Queue a)

enqueueCHANNEL :: Typeable a => a -> CHANNEL -> CHANNEL
enqueueCHANNEL a (CHANNEL xs) =
    let Just ys = cast xs
    in  CHANNEL $ Q.enqueue a ys

dequeueCHANNEL :: Typeable a => Channel' a -> CHANNEL -> Maybe (a, CHANNEL)
dequeueCHANNEL _ (CHANNEL q) = case Q.dequeue q of
    Nothing      -> Nothing
    Just (b, q') ->
        let Just a = cast b
        in  Just (a, CHANNEL q')

data ThreadState =
      Active
    | Expecting Int
    | Delayed Microseconds
    deriving Show

type M m = ThreadT ThreadId' Channel' m

data Continuation m where
    Continuation :: Typeable a => ThreadId' -> (a -> M m ()) -> Continuation m

callContinuation :: Typeable a => Continuation m -> a -> M m ()
callContinuation (Continuation _ k) a =
    let Just b = cast a
    in  k b

data SimState m = SimState
    { ssTime          :: Microseconds
    , ssNextThreadId  :: ThreadId'
    , ssNextChannelId :: Int
    , ssThreads       :: Map ThreadId' ThreadState
    , ssActive        :: Queue (ThreadId', M m ())
    , ssExpecting     :: Map Int (Continuation m)
    , ssDelayed       :: TimeQueue (ThreadId', M m ())
    , ssChannels      :: Map Int CHANNEL
    }

initialState :: SimState m
initialState = SimState
    { ssTime          = 0
    , ssNextThreadId  = ThreadId' 1
    , ssNextChannelId = 0
    , ssThreads       = M.empty
    , ssActive        = Q.empty
    , ssExpecting     = M.empty
    , ssDelayed       = T.empty
    , ssChannels      = M.empty
    }

type S m a = StateT (SimState m) m a

step :: forall m. Monad m => ThreadId' -> M m () -> S m ()
step tid (ThreadT (FreeT t)) = do
    f <- lift t
    case f of
        Pure ()              -> return ()
        Free (GetThreadId k) -> step tid $ ThreadT $ k tid
        Free (Fork t' k)     -> do
            tid'@(ThreadId' n) <- gets ssNextThreadId
            modify $ \ss -> ss
                { ssNextThreadId = ThreadId' $ n + 1
                , ssThreads      = M.insert tid' Active $ ssThreads ss
                , ssActive       = Q.enqueue (tid', t') $ ssActive ss
                }
            step tid $ ThreadT $ k tid'
        Free (Kill tid' t')  -> do
            ts <- gets ssThreads
            case M.lookup tid' ts of
                Nothing -> return ()
                Just st -> do
                    modify $ \ss -> ss {ssThreads = M.delete tid' ts}
                    modify $ \ss -> case st of
                        Active        -> ss {ssActive = Q.delete' ((== tid') . fst) $ ssActive ss}
                        Expecting cid -> ss {ssExpecting = M.delete cid $ ssExpecting ss}
                        Delayed s     -> ss {ssDelayed = T.delete' s ((== tid') . fst) $ ssDelayed ss}
            step tid $ ThreadT t'
        Free (NewChannel k)  -> do
            n <- gets ssNextChannelId
            let c = Channel' n
            modify $ \ss -> ss
                { ssNextChannelId = n + 1
                , ssChannels      = M.insert n (emptyCHANNEL c) $ ssChannels ss
                }
            step tid $ ThreadT $ k c
        Free (Send a c t')   -> do
            e <- gets ssExpecting
            let n = channelId c
            case M.lookup n e of
                Nothing                      -> modify $ \ss -> ss {ssChannels = M.adjust (enqueueCHANNEL a) n $ ssChannels ss}
                Just k@(Continuation tid' _) -> modify $ \ss -> ss
                    { ssThreads   = M.insert tid' Active $ ssThreads ss
                    , ssActive    = Q.enqueue (tid', callContinuation k a) $ ssActive ss
                    , ssExpecting = M.delete n e
                    }
            step tid $ ThreadT t'
        Free (Expect c k)    -> do
            cs <- gets ssChannels
            let n = channelId c
            let h = cs M.! n
            case dequeueCHANNEL c h of
                Just (a, h') -> do
                    modify $ \ss -> ss {ssChannels = M.insert n h' $ ssChannels ss}
                    step tid $ ThreadT $ k a
                Nothing      -> modify $ \ss -> ss {ssExpecting = M.insert n (Continuation tid $ ThreadT . k) $ ssExpecting ss}
        Free (GetTime k)     -> gets ssTime >>= step tid . ThreadT . k
        Free (Delay d t')    -> do
            s <- gets ssTime
            let s' = s + d
            modify $ \ss -> ss
                { ssThreads = M.insert tid (Delayed s') $ ssThreads ss
                , ssDelayed = T.enqueue s' (tid, ThreadT t') $ ssDelayed ss
                }

simulateFor :: forall m. Monad m => Maybe Microseconds -> M m () -> m ()
simulateFor mms = go initialState $ ThreadId' 0
  where
    go :: SimState m -> ThreadId' -> M m () -> m ()
    go s tid t = when (((>= ssTime s) <$> mms) /= Just False) $ do
        s' <- execStateT (step tid t) s
        case (Q.dequeue $ ssActive s', T.dequeue $ ssDelayed s') of
            (Just ((tid', t'), q), _)            -> do
                let s'' = s'
                        { ssThreads = M.delete tid' $ ssThreads s'
                        , ssActive  = q
                        }
                go s'' tid' t'
            (Nothing, Just (ms, (tid', t'), tq)) -> do
                let s'' = s'
                        { ssTime    = ms
                        , ssThreads = M.delete tid' $ ssThreads s'
                        , ssDelayed = tq
                        }
                go s'' tid' t'
            (Nothing, Nothing)                   -> return ()

simulate :: forall m. Monad m => M m () -> m ()
simulate = simulateFor Nothing
