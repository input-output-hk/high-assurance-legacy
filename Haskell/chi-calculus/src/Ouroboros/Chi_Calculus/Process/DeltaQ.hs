{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

module Ouroboros.Chi_Calculus.Process.DeltaQ (

    ChannelLog (..),
    Exit (..),
    deltaQ

) where

import           Prelude                                      hiding (map)

import           Control.Monad                                (foldM)

import           Data.Function                                (fix)
import           Data.Functor.Const                           (Const (Const, getConst))
import           Data.IntMap.Strict                           (IntMap)
import qualified Data.IntMap.Strict                           as IM
import           Data.List.FixedLength                        (map)
import           Data.List.NonEmpty                           (NonEmpty (..),
                                                               toList, (<|))
import           Data.Maybe                                   (catMaybes, maybe)
import           Unsafe.Coerce                                (unsafeCoerce)

import qualified Ouroboros.Chi_Calculus.Data                  as Data
import qualified Ouroboros.Chi_Calculus.Environment           as Env
import           Ouroboros.Chi_Calculus.Process               (ClosedProcess,
                                                               Process (..))
import           Ouroboros.Chi_Calculus.Process.DeltaQ.DeltaQ
import           Ouroboros.Chi_Calculus.Process.DeltaQ.HList  hiding (toList)

newtype Log d a = Log {getLog :: [(Seconds, NonEmpty (d a))]}
    deriving Show

emptyLog :: Log d a
emptyLog = Log []

insertLogEntry :: forall d a. Seconds -> d a -> Log d a -> Log d a
insertLogEntry t a l = Log $ go $ getLog l
  where
    go :: [(Seconds, NonEmpty (d a))] -> [(Seconds, NonEmpty (d a))]
    go []                   = [(t, a :| [])]
    go xs@(p@(t', ys) : zs)
        | t < t'            = (t, a :| []) : xs
        | t > t'            = p : go zs
        | otherwise         = (t, a <| ys) : zs

data ChannelLog d a = ChannelLog
    { clPast    :: Log d a
    , clReady   :: [d a]
    , clFuture  :: Log d a
    , clTime    :: Seconds
    , clChannel :: Const Int a
    } deriving Show

emptyChannelLog :: Const Int a -> Seconds -> ChannelLog d a
emptyChannelLog ch t = ChannelLog
    { clPast    = emptyLog
    , clReady   = []
    , clFuture  = emptyLog
    , clTime    = t
    , clChannel = ch
    }

advanceTime :: Seconds -> ChannelLog d a -> ChannelLog d a
advanceTime t l
    | t <  clTime l = error "can't turn back time"
    | otherwise     =
        let (xs, ys) = span (\(t', _) -> t' <= t) $ getLog $ clFuture l
        in  l { clPast   = Log $ getLog (clPast l) ++ xs
              , clReady  = clReady l ++ concat [toList das | (_, das) <- xs]
              , clFuture = Log ys
              , clTime   = t
              }

data CHANNELLOG d where
    CHANNELLOG :: ChannelLog d a -> CHANNELLOG d

earliestLogFuture :: CHANNELLOG d -> Maybe Seconds
earliestLogFuture c = case c of
    CHANNELLOG c' -> case getLog $ clFuture c' of
        []         -> Nothing
        (t, _) : _ -> Just t

newtype ChannelLogs d = ChannelLogs (IntMap (CHANNELLOG d))

emptyChannelLogs :: ChannelLogs d
emptyChannelLogs = ChannelLogs IM.empty

getChannelLog :: Const Int a -> Seconds -> ChannelLogs d -> ChannelLog d a
getChannelLog ch@(Const c) t (ChannelLogs m) = case IM.lookup c m of
    Nothing -> emptyChannelLog ch t
    Just l  -> case l of
        CHANNELLOG l' -> unsafeCoerce l'

insertChannelLog :: Const Int a -> ChannelLog d a -> ChannelLogs d -> ChannelLogs d
insertChannelLog (Const c) l (ChannelLogs m) = ChannelLogs $ IM.insert c (CHANNELLOG l) m

deleteChannelLog :: Const Int a -> ChannelLogs d -> ChannelLogs d
deleteChannelLog (Const c) (ChannelLogs m) = ChannelLogs $ IM.delete c m

newKey :: ChannelLogs d -> Const Int a
newKey (ChannelLogs m) = case IM.lookupMax m of
    Nothing     -> Const 0
    Just (c, _) -> Const (c + 1)

earliestLogsFuture :: ChannelLogs d -> Maybe Seconds
earliestLogsFuture (ChannelLogs m) =
    let xs = catMaybes $ earliestLogFuture <$> IM.elems m
    in  case xs of
            [] -> Nothing
            _  -> Just $ minimum xs

advanceTime' :: Seconds -> ChannelLogs d -> ChannelLogs d
advanceTime' t (ChannelLogs m) = ChannelLogs $ f <$> m
  where
    f :: CHANNELLOG d -> CHANNELLOG d
    f (CHANNELLOG l) = CHANNELLOG $ advanceTime t l

type Receiving dat d m a = (Const Int a, d a -> P dat d m)

data RECEIVINGS dat d m where
    RECEIVINGS :: [Receiving dat d m a] -> RECEIVINGS dat d m

newtype Receivings dat d m = Receivings (IntMap (RECEIVINGS dat d m))

sendingChannels :: ChannelLogs d -> [Int]
sendingChannels (ChannelLogs m) = fst <$> filter p (IM.toList m)
  where
    p :: (Int, CHANNELLOG d) -> Bool
    p (_, CHANNELLOG l) = case (clReady l, clFuture l) of
        ([], Log []) -> False
        _            -> True

receivingChannels :: forall dat d m. Receivings dat d m -> [Int]
receivingChannels (Receivings m) = fst <$> filter p (IM.toList m)
  where
    p :: (Int, RECEIVINGS dat d m) -> Bool
    p (_, RECEIVINGS [])      = False
    p (_, RECEIVINGS (_ : _)) = True

emptyReceivings :: Receivings dat d m
emptyReceivings = Receivings IM.empty

getReceivings :: Const Int a -> Receivings dat d m -> [Receiving dat d m a]
getReceivings (Const c) (Receivings m) = case IM.lookup c m of
    Nothing -> []
    Just rs -> case rs of
        RECEIVINGS rs' -> unsafeCoerce rs'

setReceivings :: Const Int a -> [Receiving dat d m a] -> Receivings dat d m -> Receivings dat d m
setReceivings ch [] (Receivings m) = Receivings $ IM.delete (getConst ch) m
setReceivings ch rs (Receivings m) = Receivings $ IM.insert (getConst ch) (RECEIVINGS rs) m

insertReceiving :: Const Int a -> Receiving dat d m a -> Receivings dat d m -> Receivings dat d m
insertReceiving ch r rss = setReceivings ch (r : getReceivings ch rss) rss

data Exit =
      Finished !Seconds
    | Deadlock !Seconds
    | Timeout !Seconds
    deriving (Show, Eq)

getSeconds :: Exit -> Seconds
getSeconds (Finished t) = t
getSeconds (Deadlock t) = t
getSeconds (Timeout t)  = t

data Target dat d m where
    Target :: (   Seconds
               -> Seconds
               -> ChannelLogs d
               -> Receivings dat d m
               -> [P dat d m]
               -> m (Exit, ChannelLogs d))
           -> Target dat d m

type P dat d m = Process dat (Const Int) d (Const (Target dat d m))

deltaQ :: forall m dat d ts .
          MonadDeltaQ m
       => Data.Interpretation dat d
       -> (forall a. dat d a -> DeltaQ)
       -> Seconds
       -> ClosedProcess dat ts
       -> m (Exit, HList (ChannelLog d) ts)
deltaQ dataInter dq tmax cp = (\(e, xs, _) -> (e, xs)) <$> go emptyChannelLogs cp
  where
    go :: forall ts' .
          ChannelLogs d
       -> Env.Env' (P dat d m) (Const Int) ts'
       -> m (Exit, HList (ChannelLog d) ts', ChannelLogs d)
    go ls (Env.Nil p) = do
        let Target f = deltaQ' dataInter dq p
        (ms, ls') <- f 0 tmax ls emptyReceivings []
        return (ms, Nil, ls')
    go ls (Env.Cons f) = do
        let ch  = newKey ls
            ls' = insertChannelLog ch (emptyChannelLog ch 0) ls
        (e, xs, ls'') <- go ls' $ f ch
        let l = getChannelLog ch (getSeconds e) ls''
        return (e, l ::: xs, ls'')

deltaQ' :: forall m dat d .
           MonadDeltaQ m
        => Data.Interpretation dat d
        -> (forall a. dat d a -> DeltaQ)
        -> P dat d m
        -> Target dat d m
deltaQ' dataInter dq p = Target $ \t tmax ls rs ps ->
    worker dataInter dq tmax t ls rs (p : ps)

worker :: forall m dat d .
          MonadDeltaQ m
       => Data.Interpretation dat d
       -> (forall a. dat d a -> DeltaQ)
       -> Seconds
       -> Seconds
       -> ChannelLogs d
       -> Receivings dat d m
       -> [P dat d m]
       -> m (Exit, ChannelLogs d)
worker dataInter dq tmax = go
  where
    go :: Seconds
       -> ChannelLogs d
       -> Receivings dat d m
       -> [P dat d m]
       -> m (Exit, ChannelLogs d)
    go t ls _  _
        | t > tmax                                                  = return (Timeout tmax, ls)
    go t ls rs []                                                   =
        let mt        = earliestLogsFuture ls
            (t', ls') = case mt of
                    Nothing  -> (t, ls)
                    Just t'' -> (t'', advanceTime' t' ls)
        in  go' t' ls' rs
    go t ls rs (Stop                                          : ps) = go t ls rs ps
    go t ls rs (Var (Const (Target f))                        : ps) = f t tmax ls rs ps
    go t ls rs (Letrec defs res                               : ps) =
        let p = res $ fix $ map (Const . deltaQ' dataInter dq) . defs
        in  go t ls rs (p : ps)
    go t ls rs (Parallel p1 p2                                : ps) = go t ls rs (p1 : p2 : ps)
    go t ls rs (NewChannel (cont :: Const Int a -> P dat d m) : ps) = do
        let ch  = newKey ls
            ls' = insertChannelLog ch (emptyChannelLog ch t) ls
        (t', ls'') <- go t ls' rs $ cont ch : ps
        return (t', deleteChannelLog ch ls'')
    go t ls rs (Send (ch :: Const Int a) x                     : ps) = do
        mdt <- deltaQM $ dq x
        case mdt of
            Nothing -> go t ls rs ps
            Just dt -> do
                let l   = getChannelLog ch t ls
                    l'  = l {clFuture = insertLogEntry (t + dt) (dataInter x) $ clFuture l}
                    ls' = insertChannelLog ch l' ls
                go t ls' rs ps
    go t ls rs (Receive ch r                                   : ps) =
        go t ls (insertReceiving ch (ch, r) rs) ps

    go' :: Seconds
        -> ChannelLogs d
        -> Receivings dat d m
        -> m (Exit, ChannelLogs d)
    go' t ls@(ChannelLogs logs) rs = do
        (ls'', rs', ps) <- foldM f (ls, rs, []) $ IM.elems logs
        case ps of
            [] -> do
                    let rcs = receivingChannels rs'
                        scs = sendingChannels ls''
                    case rcs of
                        []                         -> return (Finished t, ls'')
                        _
                            | any (`elem` scs) rcs -> go t ls'' rs' []
                            | otherwise            -> return (Deadlock t, ls'')
            _  -> go t ls'' rs' ps
      where
        f :: (ChannelLogs d, Receivings dat d m, [P dat d m])
          -> CHANNELLOG d
          -> m (ChannelLogs d, Receivings dat d m, [P dat d m])
        f acc@(ls', rs', ps') cl = case cl of
            CHANNELLOG l -> case clReady l of
                []       -> return acc
                (d : ds) -> do
                    let ch = clChannel l
                    case getReceivings ch rs' of
                        []       -> return acc
                        (y : ys) -> do
                            (d', ds') <- split $ d :| ds
                            let l''  = l {clReady = maybe [] toList ds'}
                                ls'' = insertChannelLog ch l'' ls'
                            ((_, cont), mzs) <- split (y :| ys)
                            let p    = cont d'
                                zs   = maybe [] toList mzs
                                rs'' = setReceivings ch zs rs'
                            return (ls'', rs'', p : ps')
