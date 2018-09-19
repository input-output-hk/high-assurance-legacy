{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

module Process
    ( Chan
    , PrCont (..)
    , Process (..)
    , ChannelState (..)
    , Message (..)
    , Environment (..)
    , ToQueue
    , toQueue
    ) where

import           Data.DeltaQ
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import           Data.List.NonEmpty (NonEmpty (..), (<|))
import           Text.Printf

type Chan = Int

newtype PrCont dq a = PrCont {runPrCont :: a -> Process dq}

instance Show (PrCont dq a) where
    show = const "PrCont[..]"

data Process dq =
      Stop
    | Chan :<: (dq, String)
    | Chan :>: PrCont dq String
    | Process dq :|: Process dq
    | Nu (PrCont dq Chan)
    deriving Show

data ChannelState dq =
      Inert
    | Full (NonEmpty String)
    | Waiting (NonEmpty (PrCont dq String))

instance Show (ChannelState dq) where

    showsPrec _ Inert        = showString "Inert"
    showsPrec d (Full xs)    = showParen (d > 10) $ showString "Full " . showsPrec 11 xs
    showsPrec d (Waiting cs) = showParen (d > 10) $
        showString $ printf "Waiting[%d]" $ length cs

data Message = Message
    { msgChan    :: !Int
    , msgPayload :: !String
    } deriving (Show, Eq, Ord)

data Environment p t dq m = Environment
    { envChSts :: IntMap (ChannelState dq)
    , envMsgs  :: Queue p t dq m Message
    } deriving Show

emptyEnvironment :: Monad m => Environment p t dq m
emptyEnvironment = Environment
    { envChSts = IM.empty
    , envMsgs  = emptyQueue
    }

stepProcess :: forall p t dq m .
               (DeltaQ p t dq, MonadProb p m)
            => Process dq
            -> Environment p t dq m
            -> m (Environment p t dq m)
stepProcess Stop env = return env

stepProcess (ch :<: (dq, s)) env = do
    let q = enqueue dq (Message ch s) $ envMsgs env
    return $ env {envMsgs = q}

stepProcess (p :|: q) env = stepProcess p env >>= stepProcess q

stepProcess (ch :>: cont) env = do
    let chsts = envChSts env
    (chst, mp) <- f (chsts IM.! ch)
    let env' = env {envChSts = IM.insert ch chst chsts}
    case mp of
        Nothing -> return env'
        Just p  -> stepProcess p env'
  where
    f :: ChannelState dq -> m (ChannelState dq, Maybe (Process dq))
    f Inert        = return (Waiting $ cont :| [], Nothing)
    f (Waiting cs) = return (Waiting $ cont <| cs, Nothing)
    f (Full xs)    = do
        (x, xs') <- pick xs
        let mp = Just $ runPrCont cont x
        return $ case xs' of
            []          -> (Inert            , mp)
            (x' : xs'') -> (Full (x' :| xs''), mp)

stepProcess (Nu cont) env = do
    let (env', ch) = newChan env
        p          = runPrCont cont ch
    stepProcess p env'

newChan :: Environment p t dq m -> (Environment p t dq m, Chan)
newChan env =
    let chsts  = envChSts env
        ch     = head [i | i <- [1..], i `IM.notMember` chsts]
        chsts' = IM.insert ch Inert chsts
        env'   = env {envChSts = chsts'}
    in  (env', ch)

class ToQueue dq a | a -> dq where
    toQueue' :: forall p t m.
                (DeltaQ p t dq, MonadProb p m)
             => a
             -> dq
             -> Environment p t dq m
             -> m [(dq, Message)]

toQueue :: (DeltaQ p t dq, MonadProb p m, ToQueue dq a) => a -> m [(dq, Message)]
toQueue p = toQueue' p (exact now) emptyEnvironment

instance ToQueue dq (Process dq) where

    toQueue' :: forall p t m.
                (DeltaQ p t dq, MonadProb p m)
             => Process dq
             -> dq
             -> Environment p t dq m
             -> m [(dq, Message)]
    toQueue' p dq env = stepProcess p env >>= go dq
      where
        go :: dq -> Environment p t dq m -> m [(dq, Message)]
        go dq' env' = do
            m <- dequeue $ envMsgs env'
            case m of
                Nothing             -> return []
                Just (dq'', msg, q) -> do
                    (env'', mp)    <- processMessage msg $ env' {envMsgs = q}
                    env'''         <- case mp of
                        Nothing -> return env''
                        Just p' -> stepProcess p' env''
                    xs             <- go (dq' <> dq'') env'''
                    return $ if msgChan msg `IM.member` envChSts env
                        then (dq', msg) : xs
                        else xs

processMessage :: forall p t dq m .
                  (DeltaQ p t dq, MonadProb p m)
               => Message
               -> Environment p t dq m
               -> m (Environment p t dq m, Maybe (Process dq))
processMessage (Message ch msg) env = do
    let chsts = envChSts env
    (chst, mp) <- f $ chsts IM.! ch
    return (env {envChSts = IM.insert ch chst chsts}, mp)
  where
    f :: ChannelState dq -> m (ChannelState dq, Maybe (Process dq))
    f Inert        = return (Full $ msg :| [], Nothing)
    f (Full xs)    = return (Full $ msg <| xs, Nothing)
    f (Waiting cs) = do
        (c, cs') <- pick cs
        let chst = case cs' of
                []          -> Inert
                (c' : cs'') -> Waiting $ c' :| cs''
        return (chst, Just $ runPrCont c msg)

instance ToQueue dq a => ToQueue dq (Chan -> a) where

    toQueue' f dq env =
        let (env', ch) = newChan env
        in  toQueue' (f ch) dq env'
