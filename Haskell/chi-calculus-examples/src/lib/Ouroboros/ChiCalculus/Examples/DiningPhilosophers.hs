{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
module Ouroboros.ChiCalculus.Examples.DiningPhilosophers (

    LoggerMsg (LogMsg),
    Data (StringLit, (:<>:), Log, Logger, DVar),
    log,
    eval,
    runWithLogger,
    Person,
    diningPhilosophers,
    defaultPhilosophers

) where

import Prelude hiding (log)

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, takeMVar, putMVar)
import Control.Monad (forever, void)

import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.List (zipWith5)
import Data.List.NonEmpty (NonEmpty ((:|)), toList)
import Data.String (IsString (fromString))

import Ouroboros.ChiCalculus.Data (
           Interpretation,
           VarData (dvar)
       )
import Ouroboros.ChiCalculus.Process (
           Process (..),
           Channel,
           ClosedProcess,
           interpret,
           parallel,
           newChannels,
           pfix,
           (<#)
       )
import Ouroboros.ChiCalculus.Process.Run (
           run
       )

infixr 6 :<>:

data LoggerMsg = LogMsg String (Channel ())

data Data (d :: Type -> Type) (a :: Type) where

    StringLit :: String -> Data d String

    (:<>:)    :: Data d String -> Data d String -> Data d String

    Log       :: Data d String -> Data d (Channel ()) -> Data d LoggerMsg

    Logger    :: Data d (Channel LoggerMsg)

    DVar      :: d a -> Data d a

instance IsString (Data d String) where

    fromString = StringLit

instance VarData Data where

    dvar = DVar

log :: Data d String -> Process Data d p -> Process Data d p
log line cnt = Logger <# Log line $ \ _ -> cnt

eval :: Channel LoggerMsg -> Interpretation Data Identity
eval logger = worker

    where

    worker :: Interpretation Data Identity
    worker (StringLit staticStr) = Identity $ staticStr
    worker (str1 :<>: str2)      = Identity $ runIdentity (worker str1) <>
                                              runIdentity (worker str2)
    worker (Log line resp)       = Identity $ LogMsg (runIdentity (worker line))
                                                     (runIdentity (worker resp))
    worker Logger                = Identity $ logger
    worker (DVar meaning)        = meaning

runWithLogger :: ClosedProcess Data -> IO ()
runWithLogger prc = do
    logger <- newEmptyMVar
    void $ forkIO $ forever $ do
        LogMsg line resp <- takeMVar logger
        putStrLn line
        putMVar resp ()
    interpret run (eval logger) prc

type Fork = String

type Person = String

tableSector :: Fork
            -> d (Channel Fork)
            -> d (Channel Fork)
            -> Process Data d p
tableSector staticFork fromSector toSector =
    DVar fromSector :<: StringLit staticFork :|: worker

    where

    worker =
        pfix $ \ turn ->
        DVar toSector :>: \ fork ->
        log ("Fork " :<>: DVar fork :<>: " has been dropped.") $
        DVar fromSector :<: DVar fork :|: PVar turn

philosopher :: Person
            -> d (Channel Fork)
            -> d (Channel Fork)
            -> d (Channel Fork)
            -> d (Channel Fork)
            -> Process Data d p
philosopher staticPerson fromFst fromSnd toFst toSnd =
    pfix $ \ turn ->
    let

        acquire fromSector cnt =
            DVar fromSector :>: \ fork ->
            log (StringLit staticPerson :<>:
                 " has taken fork "     :<>:
                 DVar fork              :<>:
                 ".") $
            cnt fork

    in
    acquire fromFst $ \ fstFork ->
    acquire fromSnd $ \ sndFork ->
    log (StringLit staticPerson :<>: " is eating.") $
    DVar toFst :<: DVar fstFork :|:
    DVar toSnd :<: DVar sndFork :|:
    PVar turn

diningPhilosophers :: NonEmpty Person -> ClosedProcess Data
diningPhilosophers (toList -> staticPersons) =
    newChannels noOfPersons $ \ fromSectors ->
    newChannels noOfPersons $ \ toSectors   ->
    let

        tableSectors = parallel $
                       zipWith3 tableSector staticForks
                                            fromSectors
                                            toSectors

        leftRightPhilosophers = parallel $
                                zipWith5 philosopher (init staticPersons)
                                                     (init fromSectors)
                                                     (tail fromSectors)
                                                     (init toSectors)
                                                     (tail toSectors)

        rightLeftPhilosopher = philosopher (last staticPersons)
                                           (head fromSectors)
                                           (last fromSectors)
                                           (head toSectors)
                                           (last toSectors)

    in
    tableSectors :|: leftRightPhilosophers :|: rightLeftPhilosopher

    where

    noOfPersons = length staticPersons

    staticForks = map show [1 .. noOfPersons]

defaultPhilosophers :: NonEmpty Person
defaultPhilosophers = "Plato" :| ["Aristotle", "Bertrand Russell", "Karl Popper"]
