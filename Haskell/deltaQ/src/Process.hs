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
    , ToTrace
    , toTrace
    ) where

import           Data.DeltaQ
import           Data.DeltaQ.PList
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import           Data.List.NonEmpty (NonEmpty (..), (<|))
import           Text.Printf

type Chan = Int

newtype PrCont dq a = PrCont {runPrCont :: a -> Process dq}

instance Show (PrCont dq a) where
    show = const "PrCont[..]"

infix 6 :<:, :>:
infixl 5 :|:

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

emptyEnvironment :: (DeltaQ p t dq, MonadProb p m) => Environment p t dq m
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
    let q = enqueue (Message ch s) dq $ envMsgs env
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

class ToTrace dq a | a -> dq where
    toTrace' :: forall p t m.
                (DeltaQ p t dq, MonadProb p m)
             => a
             -> Environment p t dq m
             -> MList m (dq, Message)

toTrace :: (DeltaQ p t dq, MonadProb p m, ToTrace dq a)
        => a
        -> MList m (dq, Message)
toTrace p = toTrace' p emptyEnvironment

instance ToTrace dq (Process dq) where

    toTrace' :: forall p t m.
                (DeltaQ p t dq, MonadProb p m)
             => Process dq
             -> Environment p t dq m
             -> MList m (dq, Message)
    toTrace' p env = MList $ stepProcess p env >>= go (exact now)
      where
        go :: dq
           -> Environment p t dq m
           -> m (Maybe ((dq, Message), MList m (dq, Message)))
        go dq env' = do
            m <- dequeue $ envMsgs env'
            case m of
                Nothing              -> return Nothing
                Just (msg, dqMsg, q) -> do
                    let dq' = dq <> dqMsg
                    (env'', mp)    <- processMessage msg $ env' {envMsgs = q}
                    env'''         <- case mp of
                        Nothing -> return env''
                        Just p' -> stepProcess p' env''
                    if msgChan msg `IM.member` envChSts env
                        then   getMList
                             $ mcons (dq', msg)
                             $ MList $ go (exact now) env'''
                        else go dq' env'''

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

instance ToTrace dq a => ToTrace dq (Chan -> a) where

    toTrace' f env =
        let (env', ch) = newChan env
        in  toTrace' (f ch) env'
