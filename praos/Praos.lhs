\documentclass{report}

\usepackage{kpfonts}
\usepackage[margin=1in]{geometry}
\usepackage{todonotes}
\usepackage{amsmath}

%include polycode.fmt

%if style == newcode
%format ^    = "''"
%format ^:   = "'':"
%format Type = "*"
%else
%format ^    = "\;{}^\prime"
%format ^:   = "\opsym{{}^\prime\ty{:}}"
%format <>   = "\mathbin{\diamond}"
%format .=   = "\mathrel{{.}\!\!=}"
%format <$>  = "\mathbin{\langle\mathdollar\rangle}"
%format Type = "\mathord{*}"
%endif

\newenvironment{codegroup}
  {\joincode\ignorespaces}
  {\endjoincode\ignorespacesafterend}

\newtheorem{property}{Property}

%if style == newcode
\begin{code}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -Wall #-}

module Main (
    -- * Prerequisites
    -- ** Random functions
    Draw(..)
  , drawRandom
  , drawFromRange
  , drawFromList
  , drawWithProbability
    -- ** Cryptographic primitives
    -- *** Hashing
  , Hash
  , hash
    -- *** PKI
  , PublicKey
  , PrivateKey
  , publicKey
  , Encrypted
  , Signed
  , encryptWith
  , decryptWith
  , signedWith
  , stripSignature
    -- *** VRF
  , Seed(..)
  , vrf
  , VrfProof(..)
  , verifyVrf
    -- ** Operational model
  , Psi(..)
  , toThread
  , evalPsi
    -- *** Stateful version
  , SPsi
  , new
  , uInp
  , uOut
  , bInp
  , bOut
  , fork
  , delay
  , psiLog
    -- *** Examples
  , ex1
    -- ** Reliability
  , DeltaQ(..)
  , miracle
  , never
  , mix
  , uniformFromZero
  , between
    -- * Algorithm independent definitions
    -- ** Protocol parameters
  , SlotNumber(..)
  , EpochNumber(..)
  , epochLength
  , activeSlotCoefficient
  , probLeader
    -- *** Properties
  , propFirstSlotEpoch
  , propLastSlotEpoch
    -- ** Data types
    -- *** Preliminaries
  , Stake(..)
  , RelativeStake(..)
    -- *** Blockchain
  , Genesis(..)
  , UnsignedBlock(..)
  , Block
  , Blockchain
    -- *** Additional accessors
  , sblockState
  , sblockSlot
  , sblockData
  , sblockProof
  , sblockNonce
  , sblockEpoch
    -- *** Transactions
  , Transaction(..)
  , applyTransaction
  , drawRandomTransaction
    -- ** Leader selection
  , askIsLeader
    -- ** Context
    -- *** Full context
  , ChainWithContext(..)
  , cwcHead
  , cwcAppend
  , chainWithContext
    -- *** Partial context
  , BlockWithPartialContext(..)
  , prevalidate
    -- ** Verification
  , VerificationFailure(..)
  , verifyChain
    -- *** Properties
  , propValidPrefix
  , propValidAppend
    -- * Broadcasting chains
  , BcMsg(..)
  , BcState(..)
  , bcStakeholder
  , bcTest
    -- * Broadcasting blocks
  , Blocks(..)
  , reconstructChains
  , BbMsg(..)
  , BbState(..)
  , bbInitState
  , bbStakeholder
    -- * Top-level application driver
  , main
  ) where

import           Control.Monad
import           Control.Monad.State.Class
import           Data.Bifunctor            (first, second)
import           Data.Bits                 (xor)
import           Data.Foldable             (fold, asum)
import           Data.List                 (maximumBy, intercalate, foldl', inits)
import           Data.Map.Strict           (Map)
import           Data.Maybe                (listToMaybe, mapMaybe)
import           Data.Monoid               ((<>))
import           Data.Ord                  (comparing)
import           Data.Set                  (Set, (\\))
import           Data.Typeable             (Typeable)
import           Generics.SOP              hiding (shift, fn, hd, S)
import           Options.Applicative       (option, auto, long, help, value, showDefault, metavar, flag')
import qualified Simulation                as SIM
import           Simulation                (Seconds)
import           System.Random             hiding (getStdGen, setStdGen)
import qualified System.Random             as RND
import           Test.QuickCheck
import qualified Data.Map.Strict           as Map
import qualified Data.Set                  as Set
import qualified GHC.Generics              as GHC
import qualified Options.Applicative       as Opt

\end{code}
%endif

\begin{document}

\title{Praos Formalization}
\author{IOHK \and Well-Typed LLP}
\maketitle

\begin{abstract}
We present a psi-calculus formalization, embedded in Haskell, of the Praos blockchain protocol \cite{praos}.
\end{abstract}

\tableofcontents


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Prerequisites
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\chapter{Prerequisites}

\todo[inline]{TODOs are marked in orange boxes.}

\section{Reading Haskell}

Haskell is a purely functional programming language; ``pure'' meaning that the same function applied to the argument must always yield the same value (and cannot access some kind of external state).
Clearly a Haskell course is outside the scope of this document; however, we provide a few pointers that hopefully will make it easier for non-Haskell programmers to read Haskell code.

\subsection{Currying}

Instead of defining $n$-ary functions such as
%
< add :: (Int, Int) -> Int
< add (x, y) = x + y
%
(a function which takes a \emph{pair} of integers and adds them together), we typically use ``currying'' and instead define
%
< add :: Int -> Int -> Int
< add x y = x + y
%
for the function which takes a \emph{single} integer $x$ and returns a \emph{function} which adds $x$ to its (single) argument. Function application is written using simple juxtaposition so that |add 1| is the function which adds 1 to its argument and |add 1 2| evaluates to 3.

\subsection{Brackets and Dollar}

Haskell programmers detest brackets and look for all kinds of ways to avoid them. A very common one is the use of the dollar (|$|) operator. So, instead of writing
%
< f x y = g (h x y)
%
we tend to write
%
< f x y = g $ h x y
%
to denote the same function.

\subsection{Monads}

Programs with actual side effects (like reading a file, printing to the console, etc.) are modelled as functions that return programs which \emph{when executed} have those side effects and then return some final value. For instance,
%
< readFile :: FilePath -> IO String
%
|readFile| is the function which, given a |FilePath|, returns a program (|IO|) that when executed returns a |String|. We then need ways to compose such programs; the primary means for doing so is through the following two combinators
%
< return  :: a -> IO a
< (>>=)   :: IO a -> (a -> IO b) -> IO b
%
It turns out that this pattern is very common, and not specific to |IO|; types (like |IO|) that support these two combinators are called \emph{monads}. Haskell has syntactic support for monads so that instead of writing
%
< foo >>= \x ->
< bar >>= \y ->
< baz x y
%
we can write
%
< do  x <- foo
<     y <- bar
<     baz x y

\section{Drawing random values}

We will only need a couple of random functions, and it is useful to enumerate them explicitly
%
\begin{codegroup}
\begin{code}
data RandomFn :: Type -> Type where
  IsLeader   :: StakeDistr -> PublicKey -> RandomFn Bool
  IsLeader'  :: RelativeStake -> RandomFn Bool
  Random     :: Random a => RandomFn a
\end{code}
%if style == newcode
\begin{code}
compareRandomFn :: RandomFn a -> RandomFn b -> Ordering
compareRandomFn (IsLeader distr key) (IsLeader distr' key') = compare (distr, key) (distr', key')
compareRandomFn IsLeader{}           IsLeader'{}            = LT
compareRandomFn IsLeader{}           Random{}               = LT
compareRandomFn IsLeader'{}          IsLeader{}             = GT
compareRandomFn (IsLeader' relStake) (IsLeader' relStake')  = compare relStake relStake'
compareRandomFn IsLeader'{}          Random{}               = LT
compareRandomFn Random               IsLeader{}             = GT
compareRandomFn Random               IsLeader'{}            = GT
compareRandomFn Random               Random                 = EQ
\end{code}
%endif
\end{codegroup}
%
The difference between |IsLeader| and |IsLeader'| is simply whether we must still
compute the relative stake or not; both are useful (in particular to support
prevalidation of blocks, see Section~\ref{sec:PartialContext}).

We can evaluate such a ``function'' given a pseudo-random number generator |StdGen|
%
\begin{codegroup}
\begin{code}
evalRandomFn :: RandomFn a -> StdGen -> a
\end{code}
%if style == newcode
\begin{code}
evalRandomFn = withGen' . go
  where
    go :: RandomFn a -> Draw a
    go (IsLeader distr key) =
        drawWithProbability $ probLeader (relativeStake key distr)
    go (IsLeader' relStake) =
        drawWithProbability $ probLeader relStake
    go Random =
        drawRandom

deriving instance Show (RandomFn a)

instance Typeable a => Summarize (RandomFn a) where
  summarize (IsLeader distr key) = summarize (distr, key)
  summarize (IsLeader' relStake) = summarize relStake
  summarize Random               = summarize ()
\end{code}
%endif
\end{codegroup}

% Helper functions for evaluating |evalRandomFn|
%if style == newcode
\begin{code}
newtype Draw a = Draw { withGen :: StdGen -> (a, StdGen) }

withGen' :: Draw a -> StdGen -> a
withGen' f = fst . withGen f

instance Functor Draw where
  fmap = liftM

instance Applicative Draw where
  pure  = return
  (<*>) = ap

instance Monad Draw where
  return a     = Draw $ (a,)
  Draw f >>= g = Draw $ (uncurry withGen . first g) . f

drawRandom :: Random a => Draw a
drawRandom = Draw random

drawFromRange :: Random a => (a, a) -> Draw a
drawFromRange = Draw . randomR

drawFromList :: [a] -> Draw a
drawFromList xs = (xs !!) <$> drawFromRange (0, length xs - 1)

drawWithProbability :: Double -> Draw Bool
drawWithProbability p = (<= p) <$> drawFromRange (0, 1)
\end{code}
%endif

\section{Cryptographic Primitives}
\label{sec:Crypto}

\subsection{Hashing}

We will simply assume that we can take the hash of any value

\begin{codegroup}
\begin{code}
newtype Hash a
\end{code}
%if style == newcode
\begin{code}
  = Hash a
  deriving (Show, Eq, Ord)

instance Typeable a => Summarize (Hash a) where
  summarize _ = "<hash>"
\end{code}
%endif
\begin{code}
hash :: a -> Hash a
\end{code}
%if style == newcode
\begin{code}
hash = Hash
\end{code}
%endif
\end{codegroup}
%
with no way of recovering $a$ from |Hash a|.

\subsection{Public-Key Infrastructure (PKI)}

%if style == newcode
\begin{code}
newtype KeyPair = KeyPair Int
  deriving (Show, Eq, Ord, Summarize)
\end{code}
%endif

Public-key encryption depends on a pair of a public key and a private key
%
\begin{codegroup}
\begin{code}
newtype PublicKey
\end{code}
%if style == newcode
\begin{code}
   = PublicKey KeyPair
   deriving (Show, Eq, Ord, Summarize)
\end{code}
%endif
\begin{code}
newtype PrivateKey
\end{code}
%if style == newcode
\begin{code}
  = PrivateKey KeyPair
  deriving (Show, Eq, Ord, Summarize)
\end{code}
%endif
\end{codegroup}
%
such that we can derive the public key from the private key
%
\begin{code}
publicKey :: PrivateKey -> PublicKey
\end{code}
%
%if style == newcode
\begin{code}
publicKey (PrivateKey k) = PublicKey k
\end{code}
%endif
%
(but not the other way around). We can encrypt a value with a public key
%
\begin{codegroup}
\begin{code}
data Encrypted a
\end{code}
%if style == newcode
\begin{code}
  = EncryptedWith { encryptedValue :: a , encryptedKey :: PublicKey }
  deriving (Eq)
\end{code}
%endif
\begin{code}
encryptWith :: a -> PublicKey -> Encrypted a
\end{code}
%if style == newcode
\begin{code}
encryptWith = EncryptedWith
\end{code}
%endif
\end{codegroup}
%
and sign it with a private key
%
\begin{codegroup}
\begin{code}
data Signed a
\end{code}
%if style == newcode
\begin{code}
  = SignedWith { signedValue :: a , signedKey :: PrivateKey  }
  deriving (Show, Eq, Ord, GHC.Generic)

instance Generic (Signed a)
instance Summarize a => Summarize (Signed a)
\end{code}
%endif
\begin{code}
signedWith :: a -> PrivateKey -> Signed a
\end{code}
%if style == newcode
\begin{code}
signedWith = SignedWith
\end{code}
%endif
\end{codegroup}
%
with corresponding ``inverse'' functions
%
\begin{code}
decryptWith     :: Encrypted  a -> PrivateKey -> Maybe a
stripSignature  :: Signed     a -> (PublicKey, a)
\end{code}

%if style == newcode
\begin{code}
decryptWith EncryptedWith{..} k =
    if encryptedKey `matchesKey` k
      then Just encryptedValue
      else Nothing

stripSignature SignedWith{..} =
    (publicKey signedKey, signedValue)

matchesKey :: PublicKey -> PrivateKey -> Bool
matchesKey (PublicKey key) (PrivateKey key') = key == key'
\end{code}
%endif

\subsection{Verifiable Random Function (VRF)}

A pseudo-random number generator needs a |Seed| as input
%
\begin{codegroup}
\begin{code}
newtype Seed
\end{code}
%if style == newcode
\begin{code}
  = Seed Int
  deriving (Show, Eq, Ord, Random, Summarize)

instance Monoid Seed where
  mempty = Seed 0
  Seed a `mappend` Seed b = Seed (a `xor` b)

genWithSeed :: Seed -> StdGen
genWithSeed (Seed s) = mkStdGen s
\end{code}
%endif
\end{codegroup}
%
Seeds form a monoid under
%
< (<>) :: Seed -> Seed -> Seed
%
We will model a VRF as a function that produces a random value $a$ given a seed and a private key
%
\begin{codegroup}
\begin{code}
vrf :: Typeable a => PrivateKey -> Seed -> RandomFn a -> (a, VrfProof)
\end{code}
%if style == newcode
\begin{code}
vrf priv@(PrivateKey (KeyPair k)) s f =
    (a, VrfProof priv s f)
  where
    gen  = genWithSeed (s <> Seed k)
    a    = evalRandomFn f gen
\end{code}
%endif
\end{codegroup}
%
along with a proof
%
\begin{codegroup}
\begin{code}
data VrfProof
\end{code}
%if style == newcode
\begin{code}
  = forall a. Typeable a => VrfProof PrivateKey Seed (RandomFn a)

deriving instance Show VrfProof

instance Eq VrfProof where
  VrfProof key seed fn == VrfProof key' seed' fn' = and [
       key  == key'
     , seed == seed'
     , compareRandomFn fn fn' == EQ
     ]
instance Ord VrfProof where
  compare (VrfProof key seed fn) (VrfProof key' seed' fn') =
    mconcat [compare key key', compare seed seed', compareRandomFn fn fn']

instance Summarize VrfProof where
  summarize (VrfProof key seed fn) = summarize (key, seed, fn)
\end{code}
%endif
\end{codegroup}
%
such that we can verify that a particular random value was produced correctly
%
\begin{codegroup}
\begin{code}
data VrfError
\end{code}
%if style == newcode
\begin{code}
  = forall a. Summarize a => VrfError a

instance Summarize VrfError where
  summarize (VrfError unexpected) = summarize unexpected

data Unexpected a =
    -- We expected |expected| and |actual| to be equal
    NotEqual {
        expected :: a
      , actual   :: a
      }

    -- We expected |actual| to be greater than or equal to |expected|
  | NotGreater {
        expected :: a
      , actual   :: a
      }

instance Summarize a => Summarize (Unexpected a) where
  summarize NotEqual{..}   = summarize expected ++ " /= " ++ summarize actual
  summarize NotGreater{..} = summarize expected ++ " >  " ++ summarize actual
\end{code}
%endif
\begin{code}
verifyVrf :: (Eq a, Summarize a) => PublicKey -> Seed -> RandomFn a -> (a, VrfProof) -> Either VrfError ()
\end{code}
%if style == newcode
\begin{code}
verifyVrf (PublicKey k) s f expected =
    if expected == actual
      then Right ()
      else Left $ VrfError NotEqual{..}
  where
    actual = vrf (PrivateKey k) s f
\end{code}
%endif
\end{codegroup}
%
(but we cannot \emph{produce} the random value given the public key only).

\section{Operational Model}

\subsection{Psi-calculus}

The psi-calculus is a parametric process calculus
\cite{DBLP:journals/corr/abs-1101-3262}, a generalization of the $\pi$-calculus.
It is very suitable for our purposes as the combination of information hiding
($\nu$ operator) with parameterization allows for convenient modelling of
cryptographic primitives; indeed, this is one of the original motivations for
the development of the psi-calculus. In addition, the psi-calculus supports a
very general notion of broadcast communication
\cite{Borgstrom:2015:BPA:2733585.2733600}.

We will use a Haskell embedding of the psi-calculus which uses only a very
basic concept of broadcast communication: we will assume a set of concurrent
top-level processes,  all of which share a single broadcast channel on which
they can both broadcast and receive. Process-internal concurrency is supported
but, in order to keep the semantics simple, internally forked processes cannot
use broadcast communication.

Having the Haskell embedding allows us to run and experiment with our models; by
using a psi-calculus as our embedded language we can use the (fully formally
verified) psi-calculus theories and the psi-calculus tool support
\cite{Borgstrom:2015:PWG:2724585.2682570} to---in principle, if not in
practice---prove equivalences between the various refinements that we make.

\subsection{Reliability}

In order to model network failure, we introduce the concept of a channel,
where for each message we can specify the probability that the recipient
will receive the message after a certain time or not at all.
%
%if style /= newcode
%format DeltaQ = "\Delta Q"
%endif
\begin{code}
newtype DeltaQ = DeltaQ (StdGen -> (Maybe Seconds, StdGen))
\end{code}
%if style == newcode
\begin{code}

instance Summarize Seconds where
    summarize = show

instance Summarize DeltaQ where
    summarize = const "ΔQ"
\end{code}
%endif
Type $\Delta Q$ represents an ``improper'' probability distribution, i.e.
one whose integral can be less than 1, where the difference to 1
represents the probability of \emph{failure}.

Deterministic |DeltaQ|'s are given by:
\begin{code}
dirac :: Maybe Seconds -> DeltaQ
dirac (Just s)
    | s < 0 = error "seconds must not be negative"
dirac s = DeltaQ $ \g -> (s, g)
\end{code}

Total reliability without delay and total unreliability
are special cases:
\begin{code}
miracle, never :: DeltaQ
miracle  = dirac $ Just 0
never    = dirac Nothing
\end{code}

$\Delta Q$ has the structure of a \emph{monoid} under sequential composition
with neutral element given by |miracle|:
\begin{code}
instance Monoid DeltaQ where
    mempty                       = miracle
    DeltaQ a `mappend` DeltaQ b  = DeltaQ $ \g ->
        let  (mda, g')   = a g
             (mdb, g'')  = b g'
             md          = (+) <$> mda <*> mdb
        in   (md, g'')
\end{code}

Given two |DeltaQ|'s and two weights,
choosing one or the other with probability proportional to the given weights
gives another |DeltaQ|:
\begin{code}
mix :: (DeltaQ, Rational) -> (DeltaQ, Rational) -> DeltaQ
(DeltaQ a, wa) `mix` (DeltaQ b, wb)
    | wa < 0 || wb < 0 || wa + wb == 0  = error "weights must not be negative, and one must be positive"
    | otherwise                         = DeltaQ $ \g ->
        let  pa       = fromRational $ wa / (wa + wb)
             (r, g')  = randomR (0 :: Double, 1) g
        in   (if r <= pa then a else b) g'
\end{code}

We will need another primitive for the construction
of |DeltaQ|'s, which represents a uniform probability distribution
between zero and a given upper bound:
\begin{code}
uniformFromZero :: Seconds -> DeltaQ
uniformFromZero s
    |  s < 0      = error "seconds must not be negative"
    |  s == 0     = miracle
    |  otherwise  = DeltaQ $ \g ->
        let (d, g')  = randomR (0 :: Double, fromRational $ toRational s) g
            md       = Just $ min s $ max 0 $ fromRational $ toRational d
        in  (md, g')
\end{code}

Combining some of these, we get, |between|,
given by the uniform distribution between a lower and upper bound:
\begin{code}
between :: (Seconds, Seconds) -> DeltaQ
between (a, b) = dirac (Just a) <> uniformFromZero (b - a)
\end{code}

\todo[inline]{For the psi-calculus model proper this would probably be
replaced with non-determinism.}

%if style == newcode
\begin{code}
type Channel = SIM.Channel

send :: Typeable a => Channel a -> DeltaQ -> a -> SIM.Thread ()
send c (DeltaQ dq) a = do
    ms <- SIM.withStdGen dq
    case ms of
        Nothing -> return ()
        Just s  -> do
            SIM.delay s
            SIM.send a c

receive :: Typeable a => Channel a -> Seconds -> SIM.Thread (Maybe a, Seconds)
receive c s = do
    start <- SIM.getTime
    ma    <- SIM.expectTimeout c s
    end   <- SIM.getTime
    return (ma, end - start)

\end{code}
%endif

\subsection{Haskell embedding}

We distinguish between one-to-one communication channels
%
\begin{codegroup}
\begin{code}
data Unicast a
\end{code}
%if style == newcode
\begin{code}
  where
    Unicast :: Summarize a => Channel a -> Unicast a
\end{code}
%endif
\end{codegroup}
%
and broadcast communication channels
%
\begin{codegroup}
\begin{code}
data Broadcast bs a
\end{code}
%if style == newcode
\begin{code}
  where
    Broadcast :: Summarize a => Ix bs a -> Broadcast bs a
\end{code}
%endif
\end{codegroup}
%
where the latter are indexed by an environment |bs| recording the types of all
available broadcast channels; we use this to disallow the use of broadcast
channels in forked processes.


The Haskell embedding of the psi-calculus is then given by
%
\begin{code}
type ProcId = String

data Psi :: [Type] -> Type where
  Done  :: Psi bs                                                                 -- completed process
  New   :: Summarize a => (Unicast a -> Psi bs) -> Psi bs                         -- create new unicast channel
  UInp  :: Unicast a -> Seconds -> ((Maybe a, Seconds) -> Psi bs) -> Psi bs       -- unicast input
  UOut  :: Unicast a -> DeltaQ -> a -> Psi bs -> Psi bs                           -- unicast output
  BInp  :: Broadcast bs a -> Seconds -> ((Maybe a ,Seconds) -> Psi bs) -> Psi bs  -- broadcast input
  BOut  :: Broadcast bs a -> DeltaQ -> a -> Psi bs -> Psi bs                      -- broadcast output
  Fork  :: ProcId -> Psi ^[] -> Psi bs -> Psi bs                                  -- fork new process
  Delay :: Seconds -> Psi bs -> Psi bs                                            -- delay
  Log   :: (Show a, Typeable a) => a -> Psi bs -> Psi bs                          -- logging
\end{code}

For unicast- and broadcast input, a \emph{timeout} is specified (as second
argument), and the continuation takes an \emph{optional} received value
(transmission can fail!) and the actual waiting time.

We will also feel free to
use the cryptographic primitives modelled in Section~\ref{sec:Crypto}; an
axiomatization of these principles (where not already available in the
literature) would need to be done when considering formal psi-calculus
definitions of our models.

\todo[inline]{The use of HOAS (functions) in our embedding makes it impossible to traverse a |Psi| term, but has as advantage that it keeps things relatively simple. If traversing |Psi| terms becomes important---for example, if we wanted to decorate processes with $\Delta$Q annotations---then we could move to PHOAS instead \cite{Oliveira:2013:ASG:2426890.2426909}.}

As stated, we can then define an interpreter over a set of top-level processes
%
\begin{code}
evalPsi :: forall bs. (SListI bs, All Typeable bs) => Seconds -> StdGen -> [(ProcId, Psi bs)] -> [SIM.LogEntry]
\end{code}
%
(the |SListI| singleton constraint is there for technical reasons only and is
always satisfied).

%if style == newcode
\begin{code}
evalPsi s g ps = fst $ SIM.simulateFor (Just s) g $ toThread ps

toThread :: forall bs.
            ( SListI bs
            , All Typeable bs
            )
         => [(ProcId, Psi bs)]
         -> SIM.Thread ()
toThread ps = do
    ps' <- forM ps $ \(i, p) -> do
        c <- hsequence' $ hcpure (Proxy :: Proxy Typeable) (Comp SIM.newChannel)
        return (i, p, c)
    let cs = map (\(_, _, c) -> c) ps'
    evalPar cs ps'

evalPar :: forall bs.
           ( SListI bs
           , All Typeable bs
           )
        => [NP Channel bs]
        -> [(ProcId, Psi bs, NP Channel bs)]
        -> SIM.Thread ()
evalPar cs ps = do
    let threads = [evalOne pid cs c psi | (pid, psi, c) <- ps]
    forM_ threads SIM.fork

evalOne :: forall bs.
           ProcId
        -> [NP Channel bs] -- ^ Write ends
        -> NP Channel bs   -- ^ Read end
        -> Psi bs          -- ^ Process to run
        -> SIM.Thread ()
evalOne pid cs c = go
  where
    go :: Psi bs -> SIM.Thread ()
    go Done = return ()
    go (New k)                     = Unicast <$> SIM.newChannel >>= go . k
    go (UInp (Unicast c') t k)     = receive c' t >>= go . k
    go (UOut (Unicast c') dq a k)  = send c' dq a >> go k
    go (BInp (Broadcast b) t k)    = receive (c `at` b) t >>= go . k
    go (BOut (Broadcast b) dq a k) = forM_ cs (\c' -> send (c' `at` b) dq a) >> go k
    go (Delay s k)                 = SIM.delay s >> go k
    go (Log a k)                   = SIM.logEntryShow (pid, a) >> go k
    go (Fork pid' psi' k)          = do
        let cs'  = replicate (length cs) Nil
            aux' = evalOne pid' cs' Nil psi'
        _ <- SIM.fork aux'
        go k

evalPsiIO :: forall bs. (SListI bs, All Typeable bs) => Seconds -> Int -> [(ProcId, Psi bs)] -> IO ()
evalPsiIO duration seed ps = do
    g <- if seed /= 0 then return (mkStdGen seed) else RND.getStdGen 
    let logs = evalPsi duration g ps
    forM_ logs print
\end{code}
%endif

\subsection{Stateful Psi}

For convenience, we will define a ``stateful psi'' layer on top of |Psi| to model processes parameterized by some state |s|. In addition, |SPsi| will be defined in continuation passing style (CPS).

\begin{code}
newtype SPsi s b a = SPsi { runSPsi :: s -> (s -> a -> Psi ^[b]) -> Psi ^[b] }
\end{code}

We can of course translate from |SPsi| to |Psi|

\begin{code}
withState :: SPsi s b () -> s -> Psi ^[b]
\end{code}

%if style == newcode
\begin{code}
SPsi f `withState` s = f s (\_s' () -> Done)
\end{code}
%endif

The advantage of using CPS is that we can now make |SPsi| an instance of a number of the standard Haskell type classes |Functor|, |Applicative|, |Monad|, |MonadIO| and |MonadState|, allowing us to write |SPsi| processes in more convenient and idiomatic manner. Of course, we can also
``lift'' the |Psi| primitives to |SPsi|:
%
\begin{codegroup}
\begin{code}
new     :: Summarize a => SPsi s b (Unicast a)
uInp    :: Unicast a -> Seconds -> SPsi s b (Maybe a, Seconds)
uOut    :: Unicast a -> DeltaQ -> a -> SPsi s b ()
bInp    :: Summarize b => Seconds -> SPsi s b (Maybe b, Seconds)
bOut    :: Summarize b => DeltaQ -> b -> SPsi s b ()
fork    :: ProcId -> Psi ^[] -> SPsi s b ()
delay   :: Seconds -> SPsi s b ()
psiLog  :: (Show a, Typeable a) => a -> SPsi s b ()
\end{code}
%if style == newcode
\begin{code}
new          = SPsi $ \s k -> New                       (k s)
uInp c t     = SPsi $ \s k -> UInp c t                  (k s)
uOut c dq a  = SPsi $ \s k -> UOut c dq a               (k s ())
bInp t       = SPsi $ \s k -> BInp (Broadcast IZ) t     (k s)
bOut dq b    = SPsi $ \s k -> BOut (Broadcast IZ) dq b  (k s ())
fork cfg p   = SPsi $ \s k -> Fork cfg p                (k s ())
delay n      = SPsi $ \s k -> Delay n                   (k s ())
psiLog a     = SPsi $ \s k -> Log a                     (k s ())

instance Functor (SPsi s b) where
  fmap = liftM

instance Applicative (SPsi s b) where
  pure  = return
  (<*>) = ap

instance Monad (SPsi s b) where
  return a = SPsi $ \s k -> k s a
  x >>= f  = SPsi $ \s k -> runSPsi x s (\s' a -> runSPsi (f a) s' k)

instance MonadState s (SPsi s b) where
  get   = SPsi $ \s k -> k s s
  put s = SPsi $ \_ k -> k s ()
\end{code}
%endif
\end{codegroup}
%
where |fork| is again a second class citizen; the forked process is not
passed any state, to avoid confusion about state propagation.

\subsection{Example}

We consider some simple (stateful) psi calculus processes. A process that outputs
a value |a| every |n| seconds is given~by

\begin{code}
every :: Summarize a => Seconds -> a -> SPsi () a ()
every n a =  forever $ do
               bOut miracle a
               delay n
\end{code}

As an example of a process with non-trivial state, the following process
increments an internal counter whenever it sees |ExTick| and prints its state on |ExShow|:

\begin{codegroup}
\begin{code}
data ExampleBroadcastMsg = ExTick | ExShow
\end{code}
%if style == newcode
\begin{code}
  deriving Show

instance Summarize ExampleBroadcastMsg where
  summarize ExTick = "tick"
  summarize ExShow = "show"
\end{code}
%endif
\begin{code}
showTicks :: SPsi Int ExampleBroadcastMsg ()
showTicks =  forever $ do
               (mmsg, _) <- bInp 10 -- 10 seconds timeout
               case mmsg of
                 Nothing      -> psiLog "timeout!"
                 Just ExTick  -> modify (+ 1)
                 Just ExShow  -> get >>= psiLog
\end{code}
\end{codegroup}

We can execute these concurrently using |evalPsi|, providing an initial state
for each process:

\begin{code}
ex1 :: [(ProcId, Psi ^[ExampleBroadcastMsg])]
ex1 =  [  ("tick1",  every 1 ExTick  `withState` ())
       ,  ("tick5",  every 5 ExShow  `withState` ())
       ,  ("show",   showTicks       `withState` 0)
       ]
\end{code}

%%
%% Auxiliary
%%

%if style == newcode

% Type-level utilities

\begin{code}
data Ix :: [Type] -> Type -> Type where
  IZ :: Ix (a:as) a
  IS :: Ix as a -> Ix (a':as) a

ix :: Ix as a -> NP f as -> f a
ix IZ     (a :* _ ) = a
ix (IS i) (_ :* as) = ix i as

at :: NP f as -> Ix as a -> f a
at = flip ix

-- absurdIx :: Ix '[] a -> b
-- absurdIx i = case i of {}
\end{code}

% Logging

\begin{code}
-- | Short, human readable, string
class Typeable a => Summarize a where
  summarize :: a -> String
  default summarize :: (Generic a, All2 Summarize (Code a)) => a -> String
  summarize = gsummarize

instance Summarize String    where summarize = id
instance Summarize Int       where summarize = show
instance Summarize Integer   where summarize = show
instance Summarize Double    where summarize = show
instance Summarize Bool      where summarize = show
instance Summarize Rational  where summarize = show

gsummarize :: (Generic a, All2 Summarize (Code a)) => a -> String
gsummarize = go . from
   where
     go :: forall xss. (All2 Summarize xss, All SListI xss) => SOP I xss -> String
     go = maybeCommaSep
        . hcollapse
        . hcmap (Proxy :: Proxy Summarize) summarizeI

     maybeCommaSep :: [String] -> String
     maybeCommaSep [s] = s
     maybeCommaSep ss  = parens (commaSep ss)

     summarizeI :: forall b. Summarize b => I b -> K String b
     summarizeI (I a) = K (summarize a)

     parens :: String -> String
     parens s = "(" ++ s ++ ")"

instance Summarize () where
  summarize () = "()"

instance (Summarize a, Summarize b) => Summarize (a, b)
instance (Summarize a, Summarize b, Summarize c) => Summarize (a, b, c)
instance (Summarize a, Summarize b, Summarize c, Summarize d) => Summarize (a, b, c, d)
instance (Summarize a, Summarize b, Summarize c, Summarize d, Summarize e) => Summarize (a, b, c, d, e)
instance (Summarize a, Summarize b, Summarize c, Summarize d, Summarize e, Summarize f) => Summarize (a, b, c, d, e, f)

instance (Summarize a, Summarize b) => Summarize (Either a b)

instance {-# OVERLAPPABLE #-} Summarize a => Summarize [a] where
  summarize = brackets . commaSep . map summarize
    where
      brackets :: String -> String
      brackets s = "[" ++ s ++ "]"

instance (Summarize k, Summarize a) => Summarize (Map k a) where
  summarize = summarize . Map.toList

instance Summarize a => Summarize (Maybe a) where
  summarize Nothing  = "Nothing"
  summarize (Just a) = summarize a

commaSep :: [String] -> String
commaSep = intercalate ","
\end{code}

% Misc

\begin{code}
whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust = forM_

repeatedly :: (a -> b -> b) -> ([a] -> b -> b)
repeatedly = flip . foldl' . flip
\end{code}

%endif


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Generic definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\chapter{Generic Definitions}

In this chapter we give definitions and functions that are independent of the
specific choice of algorithm.

\section{Protocol parameters}

We define the protocol parameters as a set of global definitions; this allows
us to tweak these parameters without having to explicitly pass them everywhere.

\begin{code}
newtype EpochNumber  = EpochNumber Integer
newtype SlotNumber   = SlotNumber Integer
\end{code}

%if style == newcode
\begin{code}
deriving instance Show      EpochNumber
deriving instance Eq        EpochNumber
deriving instance Ord       EpochNumber
deriving instance Num       EpochNumber
deriving instance Summarize EpochNumber

deriving instance Show      SlotNumber
deriving instance Eq        SlotNumber
deriving instance Ord       SlotNumber
deriving instance Num       SlotNumber
deriving instance Enum      SlotNumber
deriving instance Summarize SlotNumber
\end{code}
%endif

\begin{itemize}
\item
A transaction is declared stable if it is in a block more than $k$ blocks
deep in the ledger; we will call this |stableAfter|.
%
\begin{codegroup}
\begin{code}
stableAfter :: SlotNumber
\end{code}
%if style == newcode
\begin{code}
stableAfter = 2
\end{code}
%endif
\end{codegroup}

\item
The length of an epoch in blocks; known as $R$ in the paper.
%
\begin{codegroup}
\begin{code}
epochLength :: Integer
\end{code}
%if style == newcode
\begin{code}
epochLength = 10
\end{code}
%endif
\end{codegroup}
%
allowing us to define
%
\begin{codegroup}
\begin{code}
firstSlotInEpoch, lastSlotInEpoch :: EpochNumber -> SlotNumber
\end{code}
%if style == newcode
\begin{code}
firstSlotInEpoch (EpochNumber n) = SlotNumber (1 + epochLength * (n - 1))
lastSlotInEpoch e = firstSlotInEpoch (e + 1) - 1
\end{code}
%endif
\end{codegroup}
%
and
%
\begin{codegroup}
\begin{code}
slotEpoch :: SlotNumber -> EpochNumber
\end{code}
%if style == newcode
\begin{code}
slotEpoch (SlotNumber n) = EpochNumber ((n - 1) `div` epochLength + 1)
\end{code}
%endif
\end{codegroup}
%
where of course we must have that
%
\begin{code}
propFirstSlotEpoch, propLastSlotEpoch :: EpochNumber -> Bool
propFirstSlotEpoch  e = slotEpoch (firstSlotInEpoch  e) == e
propLastSlotEpoch   e = slotEpoch (lastSlotInEpoch   e) == e
\end{code}

\item
The active slot coefficient, referred to as $f$ in the paper,
%
\begin{codegroup}
\begin{code}
activeSlotCoefficient :: Double
\end{code}
%if style == newcode
\begin{code}
activeSlotCoefficient = 0.1
\end{code}
%endif
\end{codegroup}
%
determines the probability that a stakeholder is selected as slot leader in any given slot
%
\begin{code}
probLeader :: RelativeStake -> Double
probLeader (RelativeStake a) = 1 - ((1 - activeSlotCoefficient) ** a)
\end{code}
%
(where |**| is Haskell notation for the power function).

\item
Two special, but arbitrary, seed values that we will use
when calling the VRF in leader selection (|seedTest|) and block creation
(|seedNonce|).
%
\begin{codegroup}
\begin{code}
seedTest, seedNonce :: Seed
\end{code}
%if style == newcode
\begin{code}
seedTest  = Seed 0x63551b53
seedNonce = Seed 0x1821aea6
\end{code}
%endif
\end{codegroup}

\end{itemize}

For the definition of leader selection we will need a function to turn a slot number into a PRNG seed
%
\begin{codegroup}
\begin{code}
slotToSeed :: SlotNumber -> Seed
\end{code}
%if style == newcode
\begin{code}
slotToSeed (SlotNumber n) = Seed (fromInteger n)
\end{code}
%endif
\end{codegroup}

\section{Data types}

\subsection{Stake Distribution}

We simplify a bit from the paper and assume stakeholders have a single key that
can be used for multiple purposes. This also allows us to identify stake holders
based on their public key.

\todo[inline]{I think this simplification is fine for our current purposes; which key is used for which particular cryptographic primitive is not particularly important for the kind of refinement we want to consider here. However, if would be good if a crypto expert can verify that this simplification is unlikely to introduce subtle security flaws into our reasoning.}

For clarity's sake we will introduce some named type wrappers
%
\begin{codegroup}
\begin{code}
newtype Stake          = Stake Integer
newtype RelativeStake  = RelativeStake Double
newtype StakeDistr     = StakeDistr (Map PublicKey Stake)
\end{code}
%if style == newcode
\begin{code}
deriving instance Eq        StakeDistr
deriving instance Ord       StakeDistr
deriving instance Show      StakeDistr
deriving instance Summarize StakeDistr

deriving instance Show      Stake
deriving instance Eq        Stake
deriving instance Ord       Stake
deriving instance Num       Stake
deriving instance Random    Stake
deriving instance Summarize Stake

instance Monoid Stake where
  mempty                    = Stake 0
  Stake a `mappend` Stake b = Stake (a + b)

deriving instance Show      RelativeStake
deriving instance Summarize RelativeStake
deriving instance Eq        RelativeStake
deriving instance Ord       RelativeStake
\end{code}
%endif
\end{codegroup}

Given a stake distribution we can compute the relative stake for a particular stakeholder
%
\begin{codegroup}
\begin{code}
relativeStake :: PublicKey -> StakeDistr -> RelativeStake
\end{code}
%if style == newcode
\begin{code}
relativeStake pub (StakeDistr distr) =
    aux (distr Map.! pub) (fold distr)
  where
    aux :: Stake -> Stake -> RelativeStake
    aux (Stake ourStake) (Stake totalStake) =
      RelativeStake (fromInteger ourStake / fromInteger totalStake)
\end{code}
%endif
\end{codegroup}

\subsection{Transactions}

In order to be able to model stake evolution, we need a concrete notion of a
transaction; we will follow the paper here too (Section~3.4).
%
\begin{codegroup}
\begin{code}
data Transaction = Transaction {
       transactionFrom   :: PublicKey
    ,  transactionTo     :: PublicKey
    ,  transactionStake  :: Stake
    }
\end{code}
%if style == newcode
\begin{code}
  deriving (Show, Eq, Ord, GHC.Generic)

instance Generic   Transaction
instance Summarize Transaction
\end{code}
%endif
\end{codegroup}
%
We can apply a transaction to a stake distribution:
%
\begin{codegroup}
\begin{code}
applyTransaction :: Transaction -> StakeDistr -> StakeDistr
\end{code}
%if style == newcode
\begin{code}
applyTransaction Transaction{..} (StakeDistr distr) = StakeDistr $
       Map.alter reduceFrom   transactionFrom
    $  Map.alter incrementTo  transactionTo
    $  distr
  where
    reduceFrom, incrementTo :: Maybe Stake -> Maybe Stake

    reduceFrom Nothing    = Just (-1 * transactionStake)
    reduceFrom (Just n)   = Just (n - transactionStake)

    incrementTo Nothing   = Just (transactionStake)
    incrementTo (Just n)  = Just (n + transactionStake)
\end{code}
%endif
\end{codegroup}
%
For testing purposes we will also find it useful to be able to generate
random transactions (which make sense given some stake distribution):
%
\begin{codegroup}
\begin{code}
drawRandomTransaction :: StakeDistr -> Draw Transaction
\end{code}
%if style == newcode
\begin{code}
drawRandomTransaction (StakeDistr distr) = do
    transactionFrom  <- drawFromList (Map.keys distr)
    transactionTo    <- drawFromList (Map.keys distr)
    transactionStake <- drawFromRange (1, distr Map.! transactionFrom)
    return Transaction{..}
\end{code}
%endif
\end{codegroup}


\subsection{Genesis block}

Conceptually, we have a genesis block at the very start of the block chain
and at the start of each epoch.
%
\begin{codegroup}
\begin{code}
data Genesis = Genesis {
     genesisDistr  :: !StakeDistr
  ,  genesisNonce  :: !Seed
  }
\end{code}
%if style == newcode
\begin{code}
  deriving (Show)
\end{code}
%endif
\end{codegroup}

\subsection{Block}

We distinguish between an \emph{unsigned block} (a block without a signature, a
concept not explicitly present in the Praos paper) and a signed block; since the
latter corresponds to the concept of a block in the paper, we will refer to a
signed block as simply a |Block|.
%
\begin{codegroup}
\begin{code}
data UnsignedBlock = Block {
     blockState  :: Maybe (Hash Block)
  ,  blockSlot   :: SlotNumber
  ,  blockData   :: [Transaction]
  ,  blockProof  :: VrfProof
  ,  blockNonce  :: (Seed, VrfProof)
  }

type Block = Signed UnsignedBlock
\end{code}
%if style == newcode
\begin{code}
deriving instance Show UnsignedBlock
deriving instance Eq   UnsignedBlock
deriving instance Ord  UnsignedBlock

instance Summarize UnsignedBlock where
  summarize Block{..} = summarize (blockSlot, blockData)
\end{code}
%endif
\end{codegroup}
%
For convenience we can also define some accessors directly on signed blocks
%
\begin{codegroup}
\begin{code}
sblockState  :: Block -> Maybe (Hash Block)
sblockSlot   :: Block -> SlotNumber
sblockData   :: Block -> [Transaction]
sblockProof  :: Block -> VrfProof
sblockNonce  :: Block -> (Seed, VrfProof)
\end{code}
%
%if style == newcode
\begin{code}
sblockState  = blockState . signedValue
sblockSlot   = blockSlot  . signedValue
sblockData   = blockData  . signedValue
sblockProof  = blockProof . signedValue
sblockNonce  = blockNonce . signedValue
\end{code}
%endif
\end{codegroup}
%
as well as
%
\begin{codegroup}
\begin{code}
sblockEpoch  :: Block -> EpochNumber
\end{code}
%if style == newcode
\begin{code}
sblockEpoch = slotEpoch . sblockSlot
\end{code}
%endif
\end{codegroup}

The state of each block is the hash of the previous one, except for the first
block (see also Section~\ref{sec:Verification}, \emph{Verification}). A block
carries its slot number because not all slots have blocks associated with them.

We can apply a block to the genesis block by applying all transactions to the
stake distribution and updating the random nonce:
%
\begin{codegroup}
\begin{code}
applyBlock :: Block -> Genesis -> Genesis
\end{code}
%if style == newcode
\begin{code}
applyBlock block Genesis{..} = Genesis {
       genesisDistr  = repeatedly applyTransaction blockData genesisDistr
    ,  genesisNonce  = genesisNonce <> fst blockNonce
    }
  where
    Block{..} = signedValue block
\end{code}
%endif
\end{codegroup}

\subsection{Blockchain}

A blockchain is simply a list of blocks
%
\begin{code}
type Blockchain = [Block]
\end{code}
%
(the blocks do need to satisfy some properties; see
Section~\ref{sec:Verification}, \emph{Verification}). We do not record the
genesis block explicitly and instead assume the genesis block is known to all
stakeholders.

We define the ``head'' of the chain to be its most recent block; note that this terminology matches the one in the paper but is opposite to usual meaning of ``head'' in Haskell
%
\begin{codegroup}
\begin{code}
chainHead :: Blockchain -> Maybe Block
\end{code}
%if style == newcode
\begin{code}
chainHead = listToMaybe . reverse
\end{code}
%endif
\end{codegroup}
%
We will need a function to prune all blocks belonging to future slots:
%
\begin{codegroup}
\begin{code}
pruneAfter :: SlotNumber -> Blockchain -> Blockchain
\end{code}
%if style == newcode
\begin{code}
pruneAfter currentSlot = filter (not . inFuture . signedValue)
  where
    inFuture :: UnsignedBlock -> Bool
    inFuture Block{..} = blockSlot > currentSlot
\end{code}
%endif
\end{codegroup}
%
Finally we can apply a block chain to the genesis block by repeatedly calling |applyBlock|
%
\begin{codegroup}
\begin{code}
applyBlockChain :: Blockchain -> Genesis -> Genesis
\end{code}
%if style == newcode
\begin{code}
applyBlockChain = repeatedly applyBlock
\end{code}
%endif
\end{codegroup}

\section{Leader Selection}
\label{sec:LeaderSelection}

A stakeholder can ask if they are a slot leader for any given nonce, stake
distribution, and slot number (note that stakeholders can only check this
for themselves, not for other stakeholders):

\begin{code}
askIsLeader :: Genesis -> SlotNumber -> PrivateKey -> Maybe VrfProof
askIsLeader Genesis{..} sl key =
    if isLeader
      then  Just isLeaderProof
      else  Nothing
  where
    isLeader       :: Bool
    isLeaderProof  :: VrfProof
    (isLeader, isLeaderProof) =
      vrf  key
           (genesisNonce <> slotToSeed sl <> seedTest)
           (IsLeader genesisDistr (publicKey key))
\end{code}

\section{Context}
\label{sec:Context}

In order to verify a block, we need some context; in particular, we need to
know the genesis with respect to which the block should be verified, and the
previous block.

\subsection{Full context}

We define a type |ChainWithContext| which decorates the block chain with
sufficient information such that we can verify the chain's head, and append new
blocks, without having to traverse the entire chain. In order to satisfy both of
these goals we record both the evolving genesis block after each block, as well
as the genesis block with respect to which that block must be satisfied (which
stays the same throughout an epoch):
%
\begin{code}
data ChainWithContext =
     Empty {
         cwcGenesisEvolving  :: Genesis
      }
  |  Append {
         cwcPrevious         :: ChainWithContext
      ,  cwcBlock            :: Block
      ,  cwcGenesisEvolving  :: Genesis
      ,  cwcGenesisEpoch     :: Genesis
      }
\end{code}
%
We can ask for the head of this chain in constant time
%
\begin{codegroup}
\begin{code}
cwcHead :: ChainWithContext -> Maybe Block
\end{code}
%if style == newcode
\begin{code}
cwcHead Empty{}     = Nothing
cwcHead Append{..}  = Just cwcBlock
\end{code}
%endif
\end{codegroup}
%
as well as append a new block, also in constant time
%
\begin{code}
cwcAppend :: ChainWithContext -> Block -> ChainWithContext
cwcAppend c b = Append {
       cwcPrevious         =  c
    ,  cwcBlock            =  b
    ,  cwcGenesisEvolving  =  applyBlock b (cwcGenesisEvolving c)
    ,  cwcGenesisEpoch     =  if not isFirstInEpoch
                                then  cwcGenesisEpoch   c
                                else  genesisNextEpoch  c
    }
  where
    isFirstInEpoch :: Bool
    isFirstInEpoch =  case cwcHead c of
                        Nothing    -> True
                        Just prev  -> sblockEpoch b > sblockEpoch prev

    genesisNextEpoch :: ChainWithContext -> Genesis
    genesisNextEpoch Empty{..}   = cwcGenesisEvolving
    genesisNextEpoch Append{..}  =
      if sblockSlot cwcBlock < firstSlotInEpoch (sblockEpoch b) - 2 * stableAfter
        then  cwcGenesisEvolving
        else  genesisNextEpoch cwcPrevious
\end{code}
%
The only complication here is that we might have to search for a block in the
previous epoch, at least $2k$ slots away, in order to find the genesis block for
the next epoch.

Computing context for each block in a chain is an expensive computation, but
this is normally something we would instead do incrementally:
%
\begin{code}
chainWithContext :: Genesis -> Blockchain -> ChainWithContext
chainWithContext genesisStart = go . reverse
  where
    go :: [Block] -> ChainWithContext
    go []      = Empty genesisStart
    go (b:bs)  = go bs `cwcAppend` b
\end{code}

\subsection{Partial context}
\label{sec:PartialContext}

We need a lot of context in order to fully verify a block. In particular, when
we receive a block from another node we cannot verify it unless we have all the
block's predecessors. This means that we have no option but to store all
incoming blocks, opening ourselves up for a denial of service attack.

We can however do a bit better. Instead of just sending a block, we can send
a block with a small amount of context: the relative stake of the node that
signed the block, as well as the random seed at the start of block's epoch.
%
\begin{code}
data BlockWithPartialContext = BlockWithPartialContext {
        bpcBlock  :: Block
     ,  bpcSeed   :: Seed
     ,  bpcStake  :: RelativeStake
     }
\end{code}
%
This gives us just enough context in order to verify that block's VRF proof:
%
\begin{codegroup}
\begin{code}
prevalidate :: BlockWithPartialContext -> Either VrfError ()
\end{code}
%if style == newcode
\begin{code}
prevalidate BlockWithPartialContext{..} =
    verifyVrf
      key
      bpcSeed
      (IsLeader' bpcStake)
      (True, blockProof)
  where
    (key, Block{..}) = stripSignature bpcBlock
\end{code}
%endif
\end{codegroup}
%
If we are sure that the block was signed by the appropriate slot leader, the
probability that the block is not in fact valid is very low (it implies a stake
holder got compromised). Of course, we do need to eventually verify that the
|bpcSeed| and |bpcStake| values shipped with the block are correct. However,
while it is true that a malicious node could try to find values of |bpcSeed| and
|bpcStake| such that it can sign the block without having the node's private
key, doing so would be a very expensive computation, thus making  a DoS attack
more expensive for the attacker than for the victim.

\section{Verification}
\label{sec:Verification}

Blocks can fail to verify for a number of reasons: the block's hash is invalid,
the VRF proofs are incorrect, or the block is improperly signed or some of the
transactions in the block are incorrect. Since transactions proper are out of
the scope of this formalization, we will focus on the first two only:
%
\begin{codegroup}
\begin{code}
data VerificationFailure =
     InvalidVrfProof VrfError
  |  InvalidState (Unexpected (Maybe (Hash Block)))
\end{code}
%if style == newcode
\begin{code}
  deriving (GHC.Generic)

instance Generic   VerificationFailure
instance Summarize VerificationFailure
\end{code}
%endif
\end{codegroup}
%
Having already computed the block's context (Section~\ref{sec:Context}), block
verification is straight-forward
%
\begin{code}
verifyCwcHead :: ChainWithContext -> Either VerificationFailure ()
verifyCwcHead Empty{}    = error "verifyCwcHead: empty chain"
verifyCwcHead Append{..} = do
    unless (blockState == prev) $
      Left $ InvalidState NotEqual {expected = prev, actual = blockState}
    first InvalidVrfProof $
      verifyIsLeader genesis blockSlot key blockProof
    first InvalidVrfProof $
      verifyVrf key (genesisNonce <> slotToSeed blockSlot <> seedNonce) Random blockNonce
  where
    genesis@Genesis{..}  = cwcGenesisEpoch
    (key, Block{..})     = stripSignature cwcBlock
    prev                 = hash <$> cwcHead cwcPrevious

isValidCwcHead :: ChainWithContext -> Bool
isValidCwcHead = either (const False) (const True) . verifyCwcHead
\end{code}
%
where the verification of the block VRF is a key component:
%
\begin{code}
verifyIsLeader :: Genesis -> SlotNumber -> PublicKey -> VrfProof -> Either VrfError ()
verifyIsLeader Genesis{..} sl key proof =
    verifyVrf
      key
      (genesisNonce <> slotToSeed sl <> seedTest)
      (IsLeader genesisDistr key)
      (True, proof)
\end{code}
%
This function is the counterpart of |askIsLeader|
(Section~\ref{sec:LeaderSelection}).

To verify an entire chain we compute context for all blocks and verify them
all individually:
%
\begin{code}
verifyCwc :: ChainWithContext -> Either VerificationFailure ()
verifyCwc Empty{}       = return ()
verifyCwc c@Append{..}  = verifyCwcHead c >> verifyCwc cwcPrevious

isValidCwc :: ChainWithContext -> Bool
isValidCwc = either (const False) (const True) . verifyCwc

verifyChain :: Genesis -> Blockchain -> Either VerificationFailure ()
verifyChain genesis = verifyCwc . chainWithContext genesis

isValidChain :: Genesis -> Blockchain -> Bool
isValidChain g = either (const False) (const True) . verifyChain g
\end{code}
%

Verification has a number of properties:

\begin{property}
If a chain is valid, all it's prefixes are valid.
%
\begin{code}
propValidPrefix :: Genesis -> Blockchain -> Property
propValidPrefix g c  =    isValidChain g c
                     ==>  forAll (elements (inits c)) (isValidChain g)
\end{code}
\label{prop:validPrefix}
\end{property}

\begin{property}
Appending a valid block to a valid chain leads to a valid chain, provided the
block's state matches the chain's head.

\begin{code}
propValidAppend :: ChainWithContext -> Block -> Property
propValidAppend c b  =    isValidCwc c && isValidCwcHead (c `cwcAppend` b)
                     ==>  isValidCwc (c `cwcAppend` b)
\end{code}
\label{prop:validAppend}
\end{property}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Broadcast chains
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\chapter{Broadcasting Chains}
\label{cpt:BroadcastingChains}

In this chapter we will the Praos protocol as it is defined in the paper.
However, we will simplify and not use evolving keys. We will use the prefix |bc|
throughout this chapter.

\section{Protocol Initialization}

Initialization of the protocol ($\mathcal{F}_\mathsf{INIT}$) will simply be represented by a given genesis block.

\section{Protocol $\pi_\mathrm{DPoS}$}

\subsection{Stakeholder state}
\label{sec:StakeholderState}

Each stakeholder has access to its own keys, the genesis block at the start of
the blockchain and the genesis block at the start of the current epoch,  the
current chain and the its internal state (hash of the last block on the chain),
as well as all the transactions and chains it has received during the current
slot.
%
\begin{codegroup}
\begin{code}
data BcState = BcState {
     bcKey             :: PrivateKey
  ,  bcGenesisStart    :: Genesis
  ,  bcGenesisCurrent  :: Genesis
  ,  bcChain           :: Blockchain
  ,  bcState           :: Maybe (Hash Block)
  ,  bcRecvChains      :: [Blockchain]
  ,  bcStdGen          :: StdGen
  }
\end{code}
%if style == newcode
\begin{code}
  deriving (GHC.Generic)
\end{code}
%endif
\end{codegroup}
%
In order to be able to define some functions that we can use in various refinements
of the algorithm, we will define some classes to allow us to abstract over
the exact shape of the stakeholder state:
%
\begin{code}
class GetGenesisStart    s where getGenesisStart    :: s -> Genesis
class GetGenesisCurrent  s where getGenesisCurrent  :: s -> Genesis
class GetKey             s where getKey             :: s -> PrivateKey
class GetChain           s where getChain           :: s -> Blockchain
class GetStdGen          s where getStdGen          :: s -> StdGen
class GetState           s where getState           :: s -> Maybe (Hash Block)

class GetGenesisCurrent  s => SetGenesisCurrent  s where setGenesisCurrent  :: Genesis  -> s -> s
class GetStdGen          s => SetStdGen          s where setStdGen          :: StdGen   -> s -> s
\end{code}
%
|BcState| is an instance of all these classes.
%
%if style == newcode
\begin{code}
instance GetGenesisStart BcState where
    getGenesisStart = bcGenesisStart

instance GetGenesisCurrent BcState where
    getGenesisCurrent = bcGenesisCurrent

instance GetKey BcState where
    getKey = bcKey

instance GetChain BcState where
    getChain = bcChain

instance GetStdGen BcState where
    getStdGen = bcStdGen

instance GetState BcState where
    getState = bcState

instance SetGenesisCurrent BcState where
    setGenesisCurrent x s = s { bcGenesisCurrent = x }

instance SetStdGen BcState where
    setStdGen x s = s { bcStdGen = x }
\end{code}
%endif
%
We can use these classes to define some trivial variations on previously defined functions that
extract their parameters from the stake holder state:
%
\begin{codegroup}
\begin{code}
askIsLeader'     :: (GetKey s, GetGenesisCurrent s) => SlotNumber -> s -> Maybe VrfProof
verifyAndPrune  :: (GetGenesisStart s) => SlotNumber -> Blockchain -> s -> Either VerificationFailure Blockchain
\end{code}
%if style == newcode
\begin{code}
askIsLeader'  sl st = askIsLeader (getGenesisCurrent st) sl (getKey st)
verifyAndPrune sl c st =
    let c' = pruneAfter sl c
    in second (const c') $ verifyChain (getGenesisStart st) c'
\end{code}
%endif
\end{codegroup}
%
Likewise, we can construct a function that builds a new block containing
the transactions in the current state
%
\begin{code}
makeBlock  ::  (GetGenesisCurrent s, GetState s, GetKey s, GetState s)
           =>  SlotNumber -> VrfProof -> [Transaction] -> s -> Block
makeBlock sl isLeader transactions st =
    block `SignedWith` (getKey st)
  where
    nonce  = genesisNonce (getGenesisCurrent st)
    block  = Block {
         blockData   = transactions
      ,  blockSlot   = sl
      ,  blockState  = getState st
      ,  blockProof  = isLeader
      ,  blockNonce  = vrf (getKey st) (nonce <> slotToSeed sl <> seedNonce) Random
      }
\end{code}
%
We can implement the chain update rule (after each slot)
%
\begin{code}
bcPickMaxValid :: BcState -> BcState
bcPickMaxValid s =
    s  {  bcChain       = bcChain'
       ,  bcState       = hash <$> chainHead bcChain'
       ,  bcRecvChains  = []
       }
  where
    bcChain' = maxValid (bcRecvChains s ++ [bcChain s])

maxValid :: [Blockchain] -> Blockchain
maxValid = maximumBy (comparing length) -- |maximumBy| breaks ties in favour of later elements
\end{code}
%
and the genesis update rule (after each epoch)
%
\begin{code}
updateGenesis  ::  (SetGenesisCurrent s, GetGenesisStart s, GetChain s)
                 =>  EpochNumber -> s -> s
updateGenesis epoch st =
    setGenesisCurrent newGenesis $ st
  where
    newGenesis :: Genesis
    newGenesis =
      applyBlockChain
        (pruneAfter (lastSlotInEpoch (epoch - 1) - 2 * stableAfter) (getChain st))
        (getGenesisStart st)
\end{code}

Finally, we can specify what the initial state for each stakeholder should look
like
%
\begin{code}
bcInitState :: PrivateKey -> Genesis -> BcState
bcInitState key genesis = BcState {
       bcKey             = key
    ,  bcGenesisStart    = genesis
    ,  bcGenesisCurrent  = genesis
    ,  bcChain           = []
    ,  bcState           = Nothing
    ,  bcRecvChains      = []
    ,  bcStdGen          = mkStdGen 1
    }
\end{code}

\subsection{Broadcast messages}
\label{sec:BroadcastMessages}

In addition to broadcasting chains, we also assume that
there is a beacon broadcasting a signal at the end of each slot.
%
\begin{codegroup}
\begin{code}
data BcMsg =
     BcChain Blockchain
  |  BcEndSlot SlotInEpoch
\end{code}
%if style == newcode
\begin{code}
  deriving (Show, GHC.Generic)

instance Generic   BcMsg
instance Summarize BcMsg
\end{code}
%endif
\end{codegroup}
%
Here too it will be useful to abstract over the precise shape of these messages
so that we can define some processes that can be used in various refinements
of the algorithm.
%
\begin{code}
class Summarize msg => InjectEndSlot msg where
  injectEndSlot :: SlotInEpoch -> msg
\end{code}
%
|BcMsg| is an instance of this class.

%if style == newcode
\begin{code}
instance InjectEndSlot BcMsg where
  injectEndSlot = BcEndSlot
\end{code}
%endif

\subsection{The stakeholder process}

The stakeholder process is defined in Figure~\ref{fig:StakeholderBlocks}. It depends
on a way to create random transactions (since the paper does not specify how
transactions make it to the slot leader, which involves various interesting
design decisions)
%
\begin{codegroup}
\begin{code}
randomTransactions :: (MonadState s m, SetStdGen s, GetGenesisStart s, GetChain s) => m [Transaction]
\end{code}
%if style == newcode
\begin{code}
randomTransactions = state $ \st ->
    let distr      = genesisDistr $
                       applyBlockChain
                         (getChain st)
                         (getGenesisStart st)
        (ts, gen') = go distr [] 1 `withGen` (getStdGen st)
    in (ts, setStdGen gen' $ st)
  where
    go :: StakeDistr -> [Transaction] -> Int -> Draw [Transaction]
    go _     acc 0 = return (reverse acc)
    go distr acc n = do
      trans <- drawRandomTransaction distr
      go (applyTransaction trans distr) (trans : acc) (n - 1)
\end{code}
%endif
\end{codegroup}


\begin{figure}[p]
\hrule
\begin{code}
bcStakeholder :: DeltaQ -> Seconds -> SPsi BcState BcMsg ()
bcStakeholder dq timeout =
    startOfSlot (SlotNumber 1)
  where
    startOfSlot :: SlotNumber -> SPsi BcState BcMsg ()
    startOfSlot sl = do
      isLeader <- gets $ askIsLeader' sl
      whenJust isLeader $ bcEmit dq sl
      mainLoop sl

    mainLoop :: SlotNumber -> SPsi BcState BcMsg ()
    mainLoop sl = do
      (mmsg, _) <- bInp timeout
      case mmsg of
        Nothing                    -> do
            psiLog "Timeout waiting for broadcast."
            mainLoop sl
        Just (BcChain c)           -> do
          isValid <- gets $ verifyAndPrune sl c
          case isValid of
            Right c'      -> do
                psiLog $ "received chain: " ++ summarize c'
                modify $ \s -> s { bcRecvChains = c' : bcRecvChains s }
            Left failure  -> psiLog $ "Received invalid chain: " ++ summarize failure
          mainLoop sl
        Just (BcEndSlot nextSlot)  -> do
          modify bcPickMaxValid
          when (firstInEpoch nextSlot) $
            modify $ updateGenesis (epochNumber nextSlot)
          startOfSlot (slotNumber nextSlot)

bcEmit :: DeltaQ -> SlotNumber -> VrfProof -> SPsi BcState BcMsg ()
bcEmit dq sl isLeader = do
    transactions  <- randomTransactions
    newBlock      <- gets $ makeBlock sl isLeader transactions
    newChain      <- gets $ \s -> bcChain s ++ [newBlock]
    psiLog $ "sending chain: " ++ summarize newChain
    bOut dq $ BcChain newChain
    modify $ \s -> s { bcChain = newChain, bcState = Just (hash newBlock) }
\end{code}
\hrule
\caption{\label{fig:StakeholderChains}Stakeholder}
\end{figure}

\section{Beacon}

In order to test the system, we need a beacon demarcating slots and epochs
%
\begin{codegroup}
\begin{code}
data SlotInEpoch = SlotInEpoch {
       epochNumber   :: EpochNumber
    ,  slotNumber    :: SlotNumber
    ,  firstInEpoch  :: Bool
    }
\end{code}
%if style == newcode
\begin{code}
  deriving (Show, GHC.Generic)

instance Generic   SlotInEpoch
instance Summarize SlotInEpoch
\end{code}
%endif
\begin{code}
slotNumbers :: [SlotInEpoch] -- infinite list of all slot numbers
\end{code}
%if style == newcode
\begin{code}
slotNumbers = go 1 1 True
  where
    go :: EpochNumber -> SlotNumber -> Bool -> [SlotInEpoch]
    go epoch slot firstInEpoch =
         SlotInEpoch epoch slot firstInEpoch
       : if slot' < firstSlotInEpoch epoch'
           then go epoch  slot' False
           else go epoch' slot' True
      where
        epoch' = epoch + 1
        slot'  = slot  + 1
\end{code}
%endif
\end{codegroup}
%
The beacon is parameterized by the length of the slot in seconds.
%
\begin{code}
beacon :: (InjectEndSlot msg) => Seconds -> SPsi () msg ()
beacon slotLength = forM_ (tail slotNumbers) $ \slotInEpoch -> do
   delay slotLength
   bOut miracle $ injectEndSlot slotInEpoch
\end{code}

\section{Testing}

We can put the beacon in parallel with a given number of stake holders and watch
the communication patterns
%
\begin{codegroup}
\begin{code}
bcTest :: CmdArgs -> [(ProcId, Psi ^[BcMsg])]
\end{code}
%if style == newcode
\begin{code}
bcTest CmdArgs{..} =
      ("beacon", beacon cmdSlotLength `withState` ())
    : [ ( "stakeholder " ++ summarize s
        , bcStakeholder cmdDeltaQBChain cmdTimeout `withState` bcInitState s testGenesis
        )
      | s <- testStakeholders
      ]
  where
    TestSetup{..} = mkTestSetup cmdNumNodes

data TestSetup = TestSetup {
      testStakeholders :: [PrivateKey]
    , testStakeDistr   :: StakeDistr
    , testGenesis      :: Genesis
    }

mkTestSetup :: Int -> TestSetup
mkTestSetup numNodes = TestSetup{..}
  where
    testStakeholders :: [PrivateKey]
    testStakeholders = [PrivateKey (KeyPair k) | k <- [1 .. numNodes]]

    testStakeDistr :: StakeDistr
    testStakeDistr = StakeDistr $ Map.fromList [ (publicKey s, 1000)
                                               | s <- testStakeholders
                                               ]

    testGenesis :: Genesis
    testGenesis = Genesis testStakeDistr (Seed 1)
\end{code}
%endif
\end{codegroup}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Broadcasting blocks
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\chapter{Broadcasting Blocks}

Transmitting the entire chain whenever a new block is published is not
realistic. The ``obvious'' improvement is simply to broadcast the new block
only. Throughout this chapter we will use the prefix |bb|.

\section{Reconstructing Chains}
\label{sec:ReconstructingChains}

When we receive blocks instead of entire chain, we inevitably end up with
missing blocks and hence with partial chains. This has two immediate
consequences: we need to be able to request missing blocks, and we need to
reconstruct chains from the blocks we have whenever we receive blocks.

We can think of chains as being represented by their chain head. At the end of
each slot, we consider \emph{all} chains represented by (reconstructed from)
potential chain heads as the chains ``received'' in that slot (in the
terminology of the paper). This considers a strictly larger set than the set of
``received'' chains in the paper, but I think this a benign difference and it is
anyhow unclear how that notion would transfer more accurately when we cannot
guarantee that blocks arrive in order.

Newly created blocks are potential chain heads, but blocks sent in request to a
node's specific requests are not (as by definition they must be another block's
predecessor).
%
\begin{codegroup}
\begin{code}
data IsPotentialHead = IsPotentialHead | NotPotentialHead
\end{code}
%if style == newcode
\begin{code}
instance Summarize IsPotentialHead where
  summarize IsPotentialHead  = "IsPotentialHead"
  summarize NotPotentialHead = "NotPotentialHead"
\end{code}
%endif
\end{codegroup}
%
We need to store all blocks that we receive, even if they don't fit our current
chain, as we might need them later (although some prevalidation might be
possible; see Section~\ref{sec:PartialContext}).
%
\begin{codegroup}
\begin{code}
data Blocks = Blocks {
       blocksPotHeads  :: Set (Hash Block)
    ,  blocksMap       :: Map (Hash Block) Block
    }

insertBlock :: IsPotentialHead -> Block -> Blocks -> Blocks
\end{code}
%if style == newcode
\begin{code}
insertBlock isPotHead b Blocks{..} = Blocks {
       blocksMap       =  Map.insert (hash b) b blocksMap
    ,  blocksPotHeads  =  updatePotHeads blocksPotHeads
    }
  where
    updatePotHeads :: Set (Hash Block) -> Set (Hash Block)
    updatePotHeads =  case isPotHead of
                        IsPotentialHead   -> Set.insert (hash b)
                        NotPotentialHead  -> id
\end{code}
%endif
\end{codegroup}
%
We can construct the set of potential chains by following backwards from the
potential chain heads (we take as additional argument a set of potential heads
to skip, which we will use to avoid reconstructing already known chains):
%
\begin{code}
reconstructChains :: Genesis -> Set (Hash Block) -> Blocks -> [Blockchain]
reconstructChains genesisStart skip Blocks{..} =
      filter (isValidChain genesisStart)
    . mapMaybe chainFrom
    $ Set.toList (blocksPotHeads \\ skip)
  where
    chainFrom :: Hash Block -> Maybe Blockchain
    chainFrom = fmap reverse . reverseChainFrom . Just

    reverseChainFrom :: Maybe (Hash Block) -> Maybe Blockchain
    reverseChainFrom Nothing   = Just []  -- We reached the start of the chain
    reverseChainFrom (Just h)  =
      case Map.lookup h blocksMap of
        Nothing  -> Nothing               -- We're missing a link in the chain
        Just b   -> (b:) <$> reverseChainFrom (sblockState b)
\end{code}

\todo[inline]{If we change the structure of |Blocks| we might be able to
avoid verifying entire chains after reconstruction.}

\todo[inline]{We may wish to remove |blocksPotHeads| from |Blocks| and introduce
that only as a separate refinement step, to make the proofs easier.}

\section{Broadcast Messages}

As discussed in Section~\ref{sec:ReconstructingChains}, nodes need the ability
to request specific blocks. Moreover, when we sent blocks we can mark them
as being potential chain heads or not (although this is strictly speaking
just an optimization).
%
\begin{codegroup}
\begin{code}
data BbMsg =
     BbBlock IsPotentialHead Block
  |  BbRequest (Hash Block)
  |  BbEndSlot SlotInEpoch
\end{code}
%if style == newcode
\begin{code}
  deriving (GHC.Generic)

instance Generic BbMsg
instance Summarize BbMsg
\end{code}
%endif
\end{codegroup}
%
As for the broadcasting chains, we will again use a beacon to demarcate slots.
%
\begin{codegroup}
\begin{code}
instance InjectEndSlot BbMsg
\end{code}
%if style == newcode
\begin{code}
  where
    injectEndSlot = BbEndSlot
\end{code}
%endif
\end{codegroup}


\section{State}

The state of the stakeholders remains almost the same; we just replace the list
of received chains |bcRecvChains| with the list of received blocks |bbBlocks|
%
\begin{code}
data BbState = BbState {
       bbKey             :: PrivateKey
    ,  bbGenesisStart    :: Genesis
    ,  bbGenesisCurrent  :: Genesis
    ,  bbChain           :: Blockchain
    ,  bbState           :: Maybe (Hash Block)
    ,  bbStdGen          :: StdGen
    ,  bbBlocks          :: Blocks
    }
\end{code}
%
|BbState| satisfies the same getter/setter type classes that |BcState| does,
and hence we can call the polymorphic functions from
Chapter~\ref{cpt:BroadcastingChains}.
%
%if style == newcode
\begin{code}
instance GetGenesisStart BbState where
    getGenesisStart = bbGenesisStart

instance GetGenesisCurrent BbState where
    getGenesisCurrent = bbGenesisCurrent

instance GetKey BbState where
    getKey = bbKey

instance GetChain BbState where
    getChain = bbChain

instance GetStdGen BbState where
    getStdGen = bbStdGen

instance GetState BbState where
    getState = bbState

instance SetGenesisCurrent BbState where
    setGenesisCurrent x s = s { bbGenesisCurrent = x }

instance SetStdGen BbState where
    setStdGen x s = s { bbStdGen = x }
\end{code}
%endif
%
State initialization also extends the initialization from the broadcasting
chains algorithm; we just need to set a (trivial) value for |bbBlocks|:
%
\begin{codegroup}
\begin{code}
bbInitState :: PrivateKey -> Genesis -> BbState
\end{code}
%if style == newcode
\begin{code}
bbInitState key genesis = BbState {
       bbKey             = key
    ,  bbGenesisStart    = genesis
    ,  bbGenesisCurrent  = genesis
    ,  bbChain           = []
    ,  bbState           = Nothing
    ,  bbStdGen          = mkStdGen 1
    ,  bbBlocks          = Blocks {
                                blocksPotHeads  = Set.empty
                             ,  blocksMap       = Map.empty
                             }
    }
\end{code}
%endif
\end{codegroup}
%
Although we do not have an explicit ``received chains'' field anymore, we
can define a derived one:
%
\begin{code}
bbRecvChains :: BbState -> [Blockchain]
bbRecvChains s = reconstructChains (bbGenesisStart s) skip (bbBlocks s)
  where
    skip :: Set (Hash Block)
    skip = case bbState s of
             Nothing  -> Set.empty        -- no current chain yet
             Just h   -> Set.singleton h  -- don't reconstruct the existing chain
\end{code}
%
The chain update rule is then almost as before:
%
\begin{code}
bbPickMaxValid :: BbState -> BbState
bbPickMaxValid s =
    s  {  bbChain   =  bcChain'
       ,  bbState   =  hash <$> chainHead bcChain'
       ,  bbBlocks  =  (bbBlocks s) { blocksPotHeads = blocksPotHeads' }
       }
  where
    bcChain'         = maxValid (bbRecvChains s ++ [bbChain s])
    blocksPotHeads'  = blocksPotHeads (bbBlocks s) \\ Set.fromList (map hash (init bcChain'))
\end{code}
%
We reduce the set of potential chain heads with all blocks in the chain we
choose, except the last (i.e., the current chain head). Those blocks will never
become a chain head:
%
\begin{itemize}
\item We already have a successor for them in the current chain.
\item Whilst they may indeed be part of a \emph{different} chain if we later
choose a different twine, we would only do that if that different twine if it is
longer than our current chain; in other words, again only when we have
(different) successors for them.
\end{itemize}

\section{Stakeholder Process}

The resulting stake holder process is defined in Figure~\ref{fig:StakeholderBlocks}.

\begin{figure}[p]
\hrule
\begin{code}
bbStakeholder :: DeltaQ -> Seconds -> SPsi BbState BbMsg ()
bbStakeholder dq timeout =
    startOfSlot (SlotNumber 1)
  where
    startOfSlot :: SlotNumber -> SPsi BbState BbMsg ()
    startOfSlot sl = do
       isLeader <- gets $ askIsLeader' sl
       whenJust isLeader $ emitBlock dq sl
       mainLoop sl

    mainLoop :: SlotNumber -> SPsi BbState BbMsg ()
    mainLoop sl = do
      (mmsg, _) <- bInp timeout
      case mmsg of
        Nothing                     -> psiLog Timeout >> mainLoop sl
        Just (BbBlock isPotHead b)  -> do
           psiLog $ ReceivedBlock b
           -- prune blocks belonging to future slots
           when (sblockSlot b <= sl) $
             modify $ \s -> s { bbBlocks = insertBlock isPotHead b (bbBlocks s) }
           -- request predecessor, if not known
           knownBlocks <- gets $ blocksMap . bbBlocks
           case sblockState b of
             Just h | not (Map.member h knownBlocks)  -> psiLog (RequestingBlock h) >> bOut dq (BbRequest h)
             _otherwise                               -> return ()
           -- continue waiting for messages
           mainLoop sl
        Just (BbEndSlot nextSlot)   -> do
          modify bbPickMaxValid
          when (firstInEpoch nextSlot) $
            modify $ updateGenesis (epochNumber nextSlot)
          startOfSlot (slotNumber nextSlot)
        Just (BbRequest h)          -> do
          psiLog $ ReceivedRequest h
          mBlock <- gets $ Map.lookup h . blocksMap . bbBlocks
          whenJust mBlock $ \b -> do
            psiLog $ AnsweringRequest h
            bOut dq $ BbBlock NotPotentialHead b
          mainLoop sl

emitBlock :: DeltaQ -> SlotNumber -> VrfProof -> SPsi BbState BbMsg ()
emitBlock dq sl isLeader = do
     transactions  <- randomTransactions
     newBlock      <- gets $ makeBlock sl isLeader transactions
     newChain      <- gets $ \s -> bbChain s ++ [newBlock]
     psiLog $ EmittingBlock newBlock
     bOut dq $ BbBlock IsPotentialHead newBlock
     modify $ \s -> s { bbChain = newChain, bbState = Just (hash newBlock) }

data LogEntry =
      Timeout
    | EmittingBlock    !Block
    | ReceivedBlock    !Block
    | RequestingBlock  !(Hash Block)
    | ReceivedRequest  !(Hash Block)
    | AnsweringRequest !(Hash Block)

instance Show LogEntry where
    show Timeout              = "timeout"
    show (EmittingBlock b)    = "emitting block (" ++ summarize b ++ ")"
    show (ReceivedBlock b)    = "received block (" ++ summarize b ++ ")"
    show (RequestingBlock h)  = "requesting block (" ++ summarize h ++ ")"
    show (AnsweringRequest h) = "answering request (" ++ summarize h ++ ")"
    show (ReceivedRequest h) = "received request (" ++ summarize h ++ ")"
\end{code}
\hrule
\caption{\label{fig:StakeholderBlocks}Stakeholder}
\end{figure}

\section{Testing}

Testing proceeds in precisely the same way as in the last chapter.

\begin{codegroup}
\begin{code}
bbTest :: CmdArgs -> [(ProcId, Psi ^[BbMsg])]
\end{code}
%if style == newcode
\begin{code}
bbTest CmdArgs{..} =
      ("beacon", beacon cmdSlotLength `withState` ())
    : [ ( "stakeholder " ++ summarize s
        , bbStakeholder cmdDeltaQBChain cmdTimeout `withState` bbInitState s testGenesis
        )
      | s <- testStakeholders
      ]
  where
    TestSetup{..} = mkTestSetup cmdNumNodes
\end{code}
%endif
\end{codegroup}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% APPLICATION
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%if style == newcode
\begin{code}
data Algorithm =
    AlgBroadChains
  | AlgBroadBlocks

data CmdArgs = CmdArgs {
      -- Algorithm
      cmdAlgorithm :: Algorithm

      -- Number of stakeholders
    , cmdNumNodes :: Int

      -- DeltaQ of chain broadcast
    , cmdDeltaQBChain :: DeltaQ

      -- Slot length
    , cmdSlotLength :: Seconds

      -- Timeout for receiving messages
    , cmdTimeout :: Seconds

      -- Simulation duration
    , cmdDuration :: Seconds

      -- Random seed
    , cmdSeed :: Int
    }

parseAlgorithm :: Opt.Parser Algorithm
parseAlgorithm = asum [
      flag' AlgBroadChains $ mconcat [
          long "broadcast-chains"
        , help "Broadcast chains (as in the paper)"
        ]
    , flag' AlgBroadBlocks $ mconcat [
          long "broadcast-blocks"
        , help "Broadcast blocks (first refinement)"
        ]
    ]

parseDeltaQ :: Opt.Parser DeltaQ
parseDeltaQ = f
    <$> (option readSeconds $ mconcat [
              long "min-latency"
            , help "minimal broadcast latency in seconds"
            , value 0
            ])
    <*> (option readSeconds $ mconcat [
              long "max-latency"
            , help "maximal broadcast latency in seconds"
            , value 0
            ])
    <*> (option auto $ mconcat [
              long "reliability"
            , help "broadcast reliability in %"
            , value 100
            ])
  where
    f :: Seconds -> Seconds -> Int -> DeltaQ
    f a b r =
        let dq = between (a, b)
            p  = fromIntegral r / 100
        in  (dq, p) `mix` (never, 1 - p)

readSeconds :: Opt.ReadM Seconds
readSeconds = do
    s <- auto
    if s < 0
        then mzero
        else return s

parseCmdArgs :: Opt.Parser CmdArgs
parseCmdArgs = CmdArgs
    <$> parseAlgorithm
    <*> (option auto $ mconcat [
            long "num-nodes"
          , help "Number of nodes (stakeholders) in the system"
          ])
    <*> parseDeltaQ
    <*> (option readSeconds $ mconcat [
            long "slot-length"
          , help "Slot length"
          , metavar "SEC"
          , value 0.5
          , showDefault
          ])
    <*> (option readSeconds $ mconcat [
            long "timeout"
          , help "Timeout for receiving messages in seconds"
          , metavar "TIMEOUT"
          , value 10
          , showDefault
          ])
    <*> (option readSeconds $ mconcat [
            long "duration"
          , help "Simulation duration in s"
          , metavar "DURATION"
          , value 60
          , showDefault
          ])
    <*> (option auto $ mconcat [
            long "seed"
          , help "Random seed"
          , metavar "SEED"
          , value 0
          , showDefault
          ])

getCmdArgs :: IO CmdArgs
getCmdArgs = Opt.execParser opts
  where
    opts = Opt.info (parseCmdArgs Opt.<**> Opt.helper) $ mconcat [
        Opt.fullDesc
      , Opt.progDesc "Ouroboros Praos Model"
      ]

main :: IO ()
main = do
    cmdArgs <- getCmdArgs
    case cmdAlgorithm cmdArgs of
      AlgBroadChains -> evalPsiIO (cmdDuration cmdArgs) (cmdSeed cmdArgs) $ bcTest cmdArgs
      AlgBroadBlocks -> evalPsiIO (cmdDuration cmdArgs) (cmdSeed cmdArgs) $ bbTest cmdArgs
\end{code}
%endif

\bibliographystyle{acm}
\bibliography{references}

-- TODO: Compare to https://github.com/leithaus/casper/blob/master/casper/docs/CasperInteraction.pdf
-- TODO: Compare to https://github.com/input-output-hk/ouroboros-spec

\end{document}
