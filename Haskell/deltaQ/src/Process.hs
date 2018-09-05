{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}

module Process
    ( Chan
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

data Process dq =
      Stop
    | Chan :<: (dq, String)
    | Chan :>: (String -> Process dq)
    | Process dq :|: Process dq
    | Nu (Chan -> Process dq)

data ChannelState dq =
      Inert
    | Full (NonEmpty String)
    | Waiting (NonEmpty (String -> Process dq))

instance Show (ChannelState dq) where

    showsPrec _ Inert        = showString "Inert"
    showsPrec d (Full xs)    = showParen (d > 10) $ showString "Full " . showsPrec 11 xs
    showsPrec d (Waiting cs) = showParen (d > 10) $
        showString $ printf "Waiting[%d]" $ length cs

data Message = Message
    { msgChan    :: !Int
    , msgPayload :: !String
    } deriving (Show, Eq, Ord)

data Environment dq m = Environment
    { envChSts :: IntMap (ChannelState dq)
    , envMsgs  :: QueueDQ m Message
    }

deriving instance Show (QueueDQ m Message) => Show (Environment dq m)

emptyEnvironment :: Monad m => Environment dq m
emptyEnvironment = Environment
    { envChSts = IM.empty
    , envMsgs  = emptyQueueDQ
    }

step :: forall p t dq m .
        MonadDeltaQ p t dq m
     => Process dq
     -> Environment dq m
     -> m (Environment dq m)
step Stop env = return env

step (ch :<: (dq, s)) env = return $
    env {envMsgs = enqueueDQ dq (Message ch s) $ envMsgs env}

step (p :|: q) env = step p env >>= step q
{-
step (p :|: q) env = coinM 0.5 (f p q) (f q p)
  where
    f :: Process dq -> Process dq -> m (Environment dq m)
    f p1 p2 = step p1 env >>= step p2
    -}

step (ch :>: cont) env = do
    (chst, mp) <- f (envChSts env IM.! ch)
    let env' = env {envChSts = IM.insert ch chst $ envChSts env}
    case mp of
        Nothing -> return env'
        Just p  -> step p env
  where
    f :: ChannelState dq -> m (ChannelState dq, Maybe (Process dq))
    f Inert        = return (Waiting $ cont :| [], Nothing)
    f (Waiting cs) = return (Waiting $ cont <| cs, Nothing)
    f (Full xs)    = do
        (x, xs') <- pick xs
        let mp = Just $ cont x
        return $ case xs' of
            []          -> (Inert            , mp)
            (x' : xs'') -> (Full (x' :| xs''), mp)

step (Nu cont) env = do
    let (env', ch) = newChan env
        p          = cont ch
    step p env'

newChan :: Environment dq m -> (Environment dq m, Chan)
newChan env =
    let chsts  = envChSts env
        ch     = head [i | i <- [1..], i `IM.notMember` chsts]
        chsts' = IM.insert ch Inert chsts
        env'   = env {envChSts = chsts'}
    in  (env', ch)

class ToQueue dq a | a -> dq where
    toQueue' :: forall p t m. MonadDeltaQ p t dq m
             => a
             -> Environment dq m
             -> QueueDQ m Message

toQueue :: (MonadDeltaQ p t dq m, ToQueue dq a) => a -> QueueDQ m Message
toQueue p = toQueue' p emptyEnvironment

instance ToQueue dq (Process dq) where

    toQueue' :: forall p t m.  MonadDeltaQ p t dq m
             => Process dq
             -> Environment dq m
             -> QueueDQ m Message
    toQueue' p env = filterDQ (\msg -> msgChan msg `IM.member` envChSts env) $
        QueueDQ $ step p env >>= go
      where
        go :: Environment dq m -> m (Maybe (Message, QueueDQ m Message))
        go env' = do
            m <- dequeueDQ $ envMsgs env'
            case m of
                Nothing       -> return Nothing
                Just (msg, q) -> do
                    let env'' = env' {envMsgs = q}
                    (env''', mp) <- processMessage msg env''
                    env''''      <- case mp of
                        Nothing -> return env'''
                        Just p' -> step p' env'''
                    return $ Just (msg, QueueDQ $ go env'''')

processMessage :: forall p t dq m .
                  MonadDeltaQ p t dq m
               => Message
               -> Environment dq m
               -> m (Environment dq m, Maybe (Process dq))
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
        return (chst, Just $ c msg)

instance ToQueue dq a => ToQueue dq (Chan -> a) where

    toQueue' f env =
        let (env', ch) = newChan env
        in  toQueue' (f ch) env'
