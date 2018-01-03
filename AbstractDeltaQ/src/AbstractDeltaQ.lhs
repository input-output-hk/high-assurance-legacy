\documentclass{article}

\usepackage{kpfonts}
\usepackage[margin=1in]{geometry}
\usepackage{todonotes}
\usepackage{amsmath}
\usepackage{mathtools}

%include polycode.fmt
%options ghci -isrc

%if style == newcode
%else
%format =~ = "\cong"
%endif

\begin{document}

%if style == newcode
\begin{code}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

module AbstractDeltaQ where

import Control.Concurrent.STM (STM)
import Control.Concurrent (threadDelay, forkIO)
import Control.Monad.Reader (Reader, runReader, ask, local)
import Data.Bifunctor
import Data.Functor.Identity
import Data.Monoid ((<>))
import Data.String
import Generics.SOP
import Text.Show.Pretty (PrettyVal(..), dumpStr)
import qualified Control.Concurrent.STM as STM
import qualified Data.Function          as Fun
import qualified GHC.Generics           as GHC
import qualified Text.Show.Pretty       as P

import Util

performClient :: Equation
performClient = export $
    new undefined           $ \c ->
    out (K "s") (toValue c) $
    inp c                   $ \(K x) ->
    (Export $ return ("P(" <> x <> ")"))

performPsiLtf :: Equation
performPsiLtf = export $
    new undefined              $ \c1 ->
    new undefined              $ \c2 ->
    out (K "s_a") (toValue c1) $
    out (K "s_b") (toValue c2) $
    inp c1                     $ \(K x1) ->
    inp c2                     $ \(K x2) ->
    (Export $ return ("P(" <> x1 <> "," <> x2 <> ")"))

performPsiFtf :: Equation
performPsiFtf = export $
    new undefined              $ \c1 ->
    new undefined              $ \c2 ->
    out (K "s_a") (toValue c1) $
    out (K "s_b") (toValue c2) $
    ftf [c1, c2]               $ \(K x) ->
    (Export $ return ("P(" <> x <> ")"))

syncGeneral :: Psi p
            => Chan p a
            -> Chan p b
            -> Chan p c
            -> Chan p d
            -> Chan p e
            -> Chan p f
            -> Chan p g
            -> Chan p h
            -> Chan p i
            -> p -> p -> p
            -> p
syncGeneral a b c d e f g h i p q r =
    sync (POP ( (a :* b :* c :* Nil) :*
                (d :* e :* f :* Nil) :*
                (g :* h :* i :* Nil) :*
                Nil )) k
  where
    k (SOP (Z _))         = p
    k (SOP (S (Z _)))     = q
    k (SOP (S (S (Z _)))) = r
    k _otherwise          = error "unreachable"

performSyncGeneralExport :: Equation
performSyncGeneralExport = export $
    syncGeneral (K "a") (K "b") (K "c")
                (K "d") (K "e") (K "f")
                (K "g") (K "h") (K "i")
                "P" "Q" "R"

performSyncGeneralDeltaQ :: Verbatim
performSyncGeneralDeltaQ = showVerbatim $
    syncGeneral (K (Var "A")) (K (Var "B")) (K (Var "C"))
                (K (Var "D")) (K (Var "E")) (K (Var "F"))
                (K (Var "G")) (K (Var "H")) (K (Var "I"))
                (Var "P") (Var "Q") (Var "R")

performInp :: Verbatim
performInp = showVerbatim . simplify $
    inp (K (Var "C")) (\_ -> Var "P")

performAll :: Verbatim
performAll = showVerbatim . simplify $
    allOf (K (Var "C") :* K (Var "D") :* K (Var "E") :* Nil) (\_ -> Var "P")

performOne :: Verbatim
performOne = showVerbatim . simplify $
    oneOf (K (Var "C") :* K (Var "D") :* K (Var "E") :* Nil) $ \ns ->
    case ns of
      Z _         -> Var "P"
      S (Z _)     -> Var "Q"
      S (S (Z _)) -> Var "R"
      _otherwise  -> error "unreachable"

performFtf :: Verbatim
performFtf = showVerbatim . simplify $
    ftf [K (Var "C"), K (Var "D")] (\_ -> Var "P")

performLtf :: Verbatim
performLtf = showVerbatim . simplify $
    ltf (K (Var "C")) (K (Var "D")) (\_ _ -> Var "P")

performGiveUpAfter :: Verbatim
performGiveUpAfter = showVerbatim . simplify $
    giveUpAfter 500000 (K (Var "C")) (Var "Perr") (\_ -> Var "Pok")

performWaitAtLeast :: Verbatim
performWaitAtLeast = showVerbatim . simplify $
    waitAtLeast 500000 (K (Var "C")) (\_ -> Var "P")

performRetryMany :: Verbatim
performRetryMany = showVerbatim . simplify $
    retryMany (Var "R") undefined [1000, 2000, 5000] (Var "Perr") (\_ -> Var "Pok")

performManualLtf :: Verbatim
performManualLtf = showVerbatim . simplify $
    manualLtf (K (Var "C")) (K (Var "D")) (\_ _ -> Var "P")

performManualFtf :: Verbatim
performManualFtf = showVerbatim . simplify $
    manualFtf (Var "X") (K (Var "C")) (K (Var "D")) (\_ -> Var "P")

performManualLtf' :: Verbatim
performManualLtf' = showVerbatim . simplify $
    manualLtf' (K (Var "C")) (K (Var "D")) (\_ _ -> Var "P")
\end{code}
%endif

\newcommand{\DeltaQ}{$\Delta$Q}
\newcommand{\psicalculus}{$\psi$-calculus}
\newcommand{\picalculus}{$\pi$-calculus}

\title{Abstract and Compositional Computation of \DeltaQ}
\author{Edsko de Vries}

\maketitle

\section{Prior Work and Motivation}

We previously explored the use of parametric higher-order abstract syntax (PHOAS
\cite{Oliveira:2013:ASG:2426890.2426909}) and a finally tagless representation
\cite{Carette:2009:FTP:1630623.1630626} of the \psicalculus{}
\cite{DBLP:journals/corr/abs-1101-3262} as a representation supporting
interpretation (simulation), pretty-printing to an external \psicalculus{}
representation (possibly embedded in Isabelle), as well as abstract
interpretation in a simplistic cost model.

Lars subsequently showed how to write a concrete interpreter for the finally
tagless representation which numerically computes the overall \DeltaQ{} of a
process, exhaustively exploring the probabilistic space (albeit still making
arbitrary decisions for non-deterministic processes). As Philipp observed, such
an interpreter would also allow us to numerically compute how the overall
\DeltaQ{} varies with the \DeltaQ{} of the components, by incrementally changing
the assumptions about those components and then recomputing the overall \DeltaQ.

In this document we will attempt define an interpreter over the \psicalculus{}
which is both abstract (can compute the \DeltaQ{} of a process without
actually running it) and compositional (can compute the \DeltaQ{} of, say,
a client process without needing the corresponding server process). The
result of this interpretation will be a term in a \DeltaQ{} algebra
which gives us a more direct way to understand how the efficiency of a
process relates to the efficiency of its components and surrounding
environment.

\section{\DeltaQ{} Algebra}
\label{sec:DeltaQAlgebra}

\subsection{Definition}

The \DeltaQ{} algebra we will be using is given by

\begin{code}
type Prob = Double

data DeltaQ =
     Exact Int                  -- Exactly $n$
  |  Var String                 -- Variable
  |  DeltaQ :> DeltaQ           -- Sequential composition
  |  Ftf [DeltaQ]               -- First-to-finish
  |  Ltf [DeltaQ]               -- Last-to-finish
  |  PChoice [(Prob, DeltaQ)]   -- Probabilistic choice
  |  DepFtf [(DeltaQ, DeltaQ)]  -- Dependent first-to-finish
\end{code}

%if style == newcode
\begin{code}
  deriving (Eq, GHC.Generic)

infixr 5 :>

instance PrettyVal DeltaQ where
  prettyVal (Exact n)     = P.Con "Exact" [prettyVal n]
  prettyVal (Var x)       = P.String x
  prettyVal (Ftf dqs)     = P.Con "Ftf"     [P.List (map prettyVal dqs)]
  prettyVal (Ltf dqs)     = P.Con "Ltf"     [P.List (map prettyVal dqs)]
  prettyVal (PChoice dqs) = P.Con "PChoice" [P.List (map prettyVal dqs)]
  prettyVal (DepFtf dqs)  = P.Con "DepFtf"  [P.List (map prettyVal dqs)]
  prettyVal (a :> b)      =
      let (dq : dqs) = concatMap collect [a, b]
      in P.InfixCons
           (prettyVal dq)
           (map (\dq' -> (":>", prettyVal dq')) dqs)
    where
      collect :: DeltaQ -> [DeltaQ]
      collect (a' :> b') = concatMap collect [a', b']
      collect dq         = [dq]

instance Show DeltaQ where
  show = dumpStr
\end{code}
%endif

Hopefully most of these are self-explanatory, but we'll highlight a few.
|Exact n| is the \DeltaQ{} distribution which is 0 for $t < n$ and 1 thereafter.
|Var| can be used to have variables in the \DeltaQ{} expression; this will be
essential for a compositional analysis. |PChoice| encodes probabilistic
choice; we can define a binary probabilistic choice operator as
%
\begin{code}
pchoice :: Prob -> DeltaQ -> DeltaQ -> DeltaQ
pchoice p a b = PChoice [(p, a), (1 - p, b)]
\end{code}

\todo[inline]{Right now we are using concrete probabilities; in the future it
will probably be necessary to change |Prob| so that we can have expressions over
variables.}

\subsection{Dependent first-to-finish}
\label{sec:DepFtf}

The dependent first-to-finish combinator |DepFtf| is the only combinator that
needs a bit more explanation. Suppose that sending a request to server $S_a$
and waiting for a response has an associated \DeltaQ{} value $A$, and similarly
for server $S_b$ with \DeltaQ{} value $B$. Then a process which sends a request
to both servers, waits for a response from either one, and then continues with
the \emph{same} continuation process no matter which server responded first has
an overall \DeltaQ{} given by

< Ftf [ A, B ] :> P

if $P$ is the \DeltaQ{} of that continuation process. However, suppose we have
a process that again waits for a response from either server, but then behaves
\emph{differently} depending on which response it got. In this case the
\DeltaQ{} of the overall process is given by

< DepFtf [ (A, Pa), (B, Pb) ]

where $P_a$ and $P_b$ are the \DeltaQ{} values associated with the two different
continuation processes. In principle |DepFtf| can be expressed in terms of
sequential composition and probabilistic choice. Algebraically, we should have
that the above |DepFtf| expression is the same as

< Ftf [ A, B ] :> PChoice [ (pa, Pa) , (pb, Pb) ]

where $p_a$ is the probability that server $S_a$ will respond first and
$p_b$ the probability that server $S_b$ will respond first; it should be
possible to compute the probabilities $p_a$ and $p_b$ from the \DeltaQ{} values
$A$ and $B$.

It follows from this identity that

<     DepFtf [ (A, P), (B, P) ]
< =~  Ftf [ A, B ] :> PChoice [ (pa, P), (pb, P )]  -- for some |pa|, |pb|
< =~  Ftf [ A, B ] :> P                             -- simplify |PChoice|

In other words, dependent first-to-finish collapses to regular first-to-finish
synchronization and sequential composition when the continuation processes are
the same. Additionally,

<     DepFtf [ (A, P) ]
< =~  Ftf [ A ] :> PChoice [ (1, P ) ]  -- in this case probability must be 1
< =~  A :> P                            -- simplify trivial |Ftf| and trivial |PChoice|

so that a trivial dependent first-to-finish synchronization of a single
``choice'' collapses to just sequential composition.

\subsection{Simplification}

We can attempt to simplify a term in the \DeltaQ{} algebra, as shown in
Figure~\ref{fig:simplify}. Each of these simplification steps corresponds to an
algebraic identity; the identifies from the previous section are included.

\todo[inline]{We don't currently attempt to derive a \emph{canonical} form
in this simplification rules.}

\begin{figure}[p]
\hrule
\begin{code}
simplify :: DeltaQ -> DeltaQ
simplify (Exact n)      = Exact n
simplify (Var x)        = Var x
simplify (PChoice dqs)  = PChoice $ map (second simplify) dqs

simplify (a :> b) =
    let  dqs   = map simplify $ concatMap collect [a, b]
         dqs'  = filter (/= Exact 0) dqs
    in foldr1 (:>) dqs'
  where
    collect :: DeltaQ -> [DeltaQ]
    collect (a' :> b')  = concatMap collect [a', b']
    collect dq          = [dq]

simplify (Ftf dqs) =
    case map simplify $ concatMap collect dqs of
      [dq]  -> dq
      dqs'  -> Ftf dqs'
  where
    collect :: DeltaQ -> [DeltaQ]
    collect (Ftf dqs')  = dqs'
    collect dq          = [dq]

simplify (Ltf dqs) =
    case map simplify $ concatMap collect dqs of
      [dq]  -> dq
      dqs'  -> Ltf dqs'
  where
    collect :: DeltaQ -> [DeltaQ]
    collect (Ltf dqs')  = dqs'
    collect dq          = [dq]

simplify (DepFtf dqs) =
    let dqs' = map (bimap simplify simplify) dqs
    in case (allEqualTo (map snd dqs'), dqs') of
      (Just p   ,  _)         -> simplify (Ftf (map fst dqs') :> p)
      (Nothing  ,  [(a, b)])  -> a :> b
      (Nothing  ,  dqs'')     -> DepFtf dqs''
\end{code}
\caption{\label{fig:simplify}Simplification of \DeltaQ{} expressions}
\hrule
\end{figure}

\pagebreak
\section{Embedding \DeltaQ{} in the \psicalculus}
\label{sec:EmbeddingDeltaQ}

\subsection{Communication Patterns}
\label{sec:CommunicationPatterns}

\DeltaQ{} gives us the improper probability distribution of how long it takes to
get from point $A$ to point $B$ \cite{pnsol:pendar2}. If we want to have an
abstract interpretation of a \psicalculus{} process in terms of \DeltaQ{}, we
need to a way to identity such points. While there is some work on type systems
specifically aimed at establishing begin and end points \cite{GORDON2003379}
(albeit in the \picalculus), I think we don't need to go there and can take
advantage of idiomatic \picalculus{}/\psicalculus{} communication patterns.

A typical request/response pattern in process calculi (from the point of view
of a client) is given by

\perform{performClient}

The client creates a new local channel, sends it to the server on some global
channel $s$, and then waits on the local channel for the result. Here's the
key idea:

\begin{quote}
\it We associate the \DeltaQ{} from request to response with the wait
for the response.
\end{quote}

We want to have a \emph{compositional} method of computing \DeltaQ{}. In
process calculi, the link between processes is given by channels. If we want
to have a means of computing the \DeltaQ{} of a client process, associating the
\DeltaQ{} of the request/response pair with only the response allows us to
do a compositional analysis of the client \emph{by annotating channels} with
\DeltaQ{}: the \DeltaQ{} associated with waiting on that channel for a response.
This is all the more reasonable when we use asynchronous communication only
(the client does not wait for the output to be delivered).

\todo[inline]{The use of asynchronous communication is actually a larger
discussion that we need to have. The more we are working on this formalization,
the more it seems to me that using asynchronous communication as our (only)
communication primitive makes more sense and is more realistic. Although the
\psicalculus{} uses synchronous point-to-point communication, we can  use the
standard encoding of asynchronous communication using the parallel combinator,
as in the example above.}

If we want to go beyond this simple ``create new channel, send, wait for
request'' pattern, there is a large body of work on session types for process
calculi that we can take advantage of (for instance, \cite{sessiontypes}; but
there many others); in the remainder of this document I will however only use
this pattern.

\subsection{The |sync| operator}
\label{sec:sync}

From a process calculus perspective, last-to-finish synchronization of two
requests to two servers $s_a$ and $s_b$ corresponds to sequential composition:

\perform{performPsiLtf}

First-to-finish synchronization corresponds to external choice; the
\psicalculus{} does not have an external choice construct, but we can encode it:

\perform{performPsiFtf}

A direct analysis of these processes in terms of \DeltaQ{} is however
non-trivial. Instead, we provide an explicit combinator |sync|\footnote{I've
called it |sync| since, like Lars' combinator, it provides a single construct
which can be used to encode both FTF and LTF; the semantics are however not the
same.} which encodes both FTF and LTF synchronization:

< sync :: Psi p => POP (Chan p) xss -> (SOP (Value p) xss -> p) -> p

We are given a product-of-product (POP) of channels
(a heterogeneous list of heterogeneous list of channels): the outer product
corresponds to a choice (FTF), the inner products correspond to the channels
we want to read from within each choice (LTF). The continuation is given
given a value of the corresponding sum-of-products, i.e., the values
that were read along with a tag indicating which branch alternative was picked
(the definition of POP and SOP come from the \texttt{generics-sop} library
\cite{deVries:2014:TSP:2633628.2633634}).

Concretely, |sync| applied to a POP
$$\bigl( (a, b, c), (d, e, f), (g, h, i) \bigr)$$
corresponds to a \psicalculus{} process

\perform{performSyncGeneralExport}

and corresponds to a \DeltaQ

\perform{performSyncGeneralDeltaQ}

where $A \ldots I$ are the \DeltaQ{} values associated with the corresponding
channels, and $P, Q, R$ are the \DeltaQ{} values associated with the three
continuation processes.

\subsection{Special cases}

In this section we consider some special cases of |sync|, along with their
\DeltaQ{} values. Note that all the \DeltaQ{} values in this section (and
almost everywhere else in this document) are computed by the abstract
interpreter.

\subsubsection{Input}

In the simplest case, |sync| just becomes the standard \psicalculus{} input
prefix:
%
\begin{code}
inp :: Psi p => Chan p a -> (Value p a -> p) -> p
inp c k = sync (toSingletonPOP c) $ k . fromSingletonSOP
\end{code}
%
so that |inp c p| has \DeltaQ

\perform{performInp}

where $C$ is the \DeltaQ{} associated with the channel and $P$ is the \DeltaQ{}
of the continuation.

\subsubsection{Multiple Inputs}

Slightly more generally, a single inner product corresponds to the sequential
composition of a number of inputs:
%
\begin{code}
allOf :: (Psi p, SListI xs) => NP (Chan p) xs -> (NP (Value p) xs -> p) -> p
allOf cs k = sync (POP (cs :* Nil)) $ \(SOP (Z xs)) -> k xs
\end{code}
%
so that |allOf (c :* d :* e :* Nil)| has \DeltaQ

\perform{performAll}

where $P$ is the \DeltaQ{} of the continuation.

\subsubsection{External Choice}
\label{sec:oneOf}

Similarly, a outer product of only singleton inner products corresponds to
external choice of the inputs:
%
\begin{code}
oneOf :: (Psi p, SListI xs) => NP (Chan p) xs -> (NS (Value p) xs -> p) -> p
oneOf cs k = rotate cs $ \cs' -> sync (POP cs') $ k . unrotate . unSOP
\end{code}
%
(we need to do a bit of juggling to get things into the right shape);
this means that |oneOf (c :* d :* e :* Nil)| has \DeltaQ

\perform{performOne}

where $P, Q, R$ are the \DeltaQ{}s of the continuations.

\subsection{Derived Combinators}

In his development where he computes \DeltaQ{} numerically, Lars defines a
number of combinators derived from his |sync| operator. We can develop
analogue combinators here, bearing in mind that their semantics don't like
up exactly.

\subsubsection{|ftf|}

The |ftf| combinator is a specialization of |oneOf| to channels of the same
type, forgetting which channel we received an input from:
%
\begin{code}
ftf :: Psi p => [Chan p a] -> (Value p a -> p) -> p
ftf cs k = toHomProd cs $ \cs' -> oneOf cs' $ k . fromHomSum
\end{code}
%
For |ftf [c, d]| we compute the \DeltaQ

\perform{performFtf}

where $P$ and $Q$ are the \DeltaQ{} values associated with the two continuation
processes; this computation depends on the simplification of a dependent
first-to-choice with identical continuations (Section~\ref{sec:DepFtf}).

\subsubsection{|lft|}

This is a straight-forward application of |allOf|:

\begin{code}
ltf :: Psi p => Chan p a -> Chan p b -> (Value p a -> Value p b -> p) -> p
ltf c c' k = allOf (c :* c' :* Nil) $ \(a :* b :* Nil) -> k a b
\end{code}

with derived \DeltaQ{}

\perform{performLtf}

\subsubsection{|giveUpAfter|}

We need to do a bit more work to define |giveUpAfter|. We first define a useful
combinator that adds a timeout argument to |sync|, given in
Figure~\ref{fig:syncTimeout}. We create a new channel, fork a new process that
writes a signal to that channel after the specified timeout, and then wait for
an input on any of the given channels or the new internal channel. The argument
to |new| is the \DeltaQ{} associated with that channel (and is simply equal to
the timeout).

\begin{figure}[t]
\hrule
\begin{code}
type Timeout = Int

syncTimeout :: (Psi p, SListI2 xss) => Timeout -> POP (Chan p) xss -> p -> (SOP (Value p) xss -> p) -> p
syncTimeout n (POP css) kErr kOk =
    new (Exact n)                   $ \c ->
    fork (signalTimeout c)          $
    sync (POP ((c :* Nil) :* css))  $ \(SOP sop) ->
    case sop of
      Z _    -> kErr
      S sop' -> kOk (SOP sop')
  where
    signalTimeout c' =
        io (threadDelay n)  $
        out c' unit         $
        done
\end{code}
\hrule
\caption{\label{fig:syncTimeout}|syncTimeout|}
\end{figure}

We can then develop variants of |oneOf| and |ftf| with support for timeout:
%
\begin{code}
oneOfTimeout :: (Psi p, SListI xs) => Timeout -> NP (Chan p) xs -> p -> (NS (Value p) xs -> p) -> p
oneOfTimeout n cs kErr kOk = rotate cs $ \cs' -> syncTimeout n (POP cs') kErr $ kOk . unrotate . unSOP

ftfTimeout :: Psi p => Timeout -> [Chan p a] -> p -> (Value p a -> p) -> p
ftfTimeout n cs kErr kOk = toHomProd cs $ \cs' -> oneOfTimeout n cs' kErr $ kOk . fromHomSum
\end{code}
%
and finally easily derive |giveUpAfter|
%
\begin{code}
giveUpAfter :: Psi p => Timeout -> Chan p a -> p -> (Value p a -> p) -> p
giveUpAfter n c = ftfTimeout n [c]
\end{code}
%
The \DeltaQ{} we compute for |giveUpAfter 500000 c| is

\perform{performGiveUpAfter}

where |Perr| is the \DeltaQ{} associated with the error continuation, and |Pok|
is the \DeltaQ{} associated with the regular continuation.

\subsubsection{|waitAtLeast|}

The |waitAtLeast| combinator is in some sense ``dual'' to |giveUpAfter|, and
we can follow a similar strategy in the implementation:

\begin{code}
waitAtLeast :: Psi p => Timeout -> Chan p a -> (Value p a -> p) -> p
waitAtLeast n c k =
    new (Exact n)            $ \c' ->
    fork (signalTimeout c')  $
    ltf c' c (const k)
  where
    signalTimeout c' =
        io (threadDelay n)  $
        out c' unit         $
        done
\end{code}

The \DeltaQ{} we compute for |waitAtLeast 500000 c| is

\perform{performWaitAtLeast}

\subsubsection{|retryMany|}

The last combinator we consider is |retryMany|. In Lars' formulation, this
retries some monadic action $n$ times, with potentially different
timeouts. In our formulation simply \emph{waiting} on the same channel a
few times with different timeouts is exactly the same thing as waiting on
that channel only once with a timeout equal to the sum of the individual
timeouts; this isn't a useful analogue. Instead, we should \emph{resend}
the request $n$ times, creating $n$ different channels, and then waiting on a
response on \emph{any} of those channels.

\begin{code}
retryMany :: forall p a. Psi p => DeltaQ -> Chan p (Chan p a) -> [Timeout] -> p -> (Value p a -> p) -> p
retryMany dq s ns kErr kOk = go [] ns
  where
    go :: [Chan p a] -> [Timeout] -> p
    go  _   []       =  kErr
    go  cs  (n:ns')  =  new dq             $ \c ->
                        out s (toValue c)  $
                        ftfTimeout n (c:cs) (go (c:cs) ns') kOk
\end{code}

If we have a server that responds to our request with a \DeltaQ{} response time
of $R$, then for |retryMany| with timeouts 1000ms, 2000ms and 5000ms we
compute the \DeltaQ{} value shown in Figure~\ref{fig:performRetryMany}.

\begin{figure}[t]
\hrule
\perform{performRetryMany}
Note: |Ftf [R, R]| is \emph{not} the same as |R|!
\hrule
\caption{\label{fig:performRetryMany}Computed \DeltaQ{} for |retryMany|}
\end{figure}


\subsection{Manual Synchronization}

We stated in Section~\ref{sec:sync} that a direct analysis of psi-calculus
processes that implement first-to-finish and last-to-finish synchronization
would be difficult, and hence we introduced the |sync| combinator. However,
since those ``manual synchronization'' patterns can of course still be
expressed, this begs the question what kind of \DeltaQ{} \emph{do} we compute
for those processes?

\subsubsection{Last-to-finish}
\label{sec:manualLtf}

We can encode the direct last-to-finish pattern as
%
\begin{code}
manualLtf :: Psi p => Chan p a -> Chan p b -> (Value p a -> Value p b -> p) -> p
manualLtf c d k = inp c $ \a -> inp d $ \b -> k a b
\end{code}
%
we compute

\perform{performManualLtf}

This is \emph{not} the same as the \DeltaQ{} computed for |ltf|, which was

\perform{performLtf}

but is nonetheless correct, if overly conversative.

\subsubsection{First-to-finish}
\label{sec:manualFtf}

Manual first-to-finish synchronization is given by
%
\begin{code}
manualFtf :: Psi p => DeltaQ -> Chan p a -> Chan p a -> (Value p a -> p) -> p
manualFtf dq c d k =
    new dq                                $ \l ->
    fork (inp c  $ \x -> out l x $ done)  $
    fork (inp d  $ \x -> out l x $ done)  $
    inp l k
\end{code}
%
The \DeltaQ{} we compute for this is

\perform{performManualFtf}

\emph{for whatever \DeltaQ{} value |X| we pass in}; the |new| construct takes
such a \DeltaQ{} argument as input and we make no attempt at inference. So,
if we let |X = Ftf [ C, D ]| then we get the same result as for |ftf|

\perform{performFtf}

but if we annotate channel $l$ incorrectly we get incorrect answers. However,
this will be true generally anyway: if a client makes incorrect assumptions
about the performance of the server, we will arrive at incorrect conclusions.

\subsubsection{Last-to-finish in terms of first-to-finish}
\label{sec:manualLtf2}

In Section~\ref{sec:oneOf} we introduced a specialization of |sync| that
encoded first-to-finish synchronization:

< oneOf :: (Psi p, SListI xs) => NP (Chan p) xs -> (NS (Value p) xs -> p) -> p

This combinator is slightly more general than |ftf| in that in addition to
the value received, the continuation is also told which channel that value came
from. Thus, we could conceivable define last-to-finish synchronization in
terms of |oneOf| as

\begin{code}
manualLtf' :: Psi p => Chan p a -> Chan p b -> (Value p a -> Value p b -> p) -> p
manualLtf' c d k =
    oneOf (c :* d :* Nil) $ \ns ->
    case ns of
      Z x      -> inp d $ \y -> k x y
      S (Z y)  -> inp c $ \x -> k x y
      S (S _)  -> error "unreachable"
\end{code}

(This closely matches how one might define last-to-finish in terms of Lars'
original |sync| operator.) The \DeltaQ{} we compute for this is

\perform{performManualLtf'}

This is equivalent (I believe) to the \DeltaQ{} value we computed for
|manualLtf| in Section~\ref{sec:manualLtf}, and hence is again correct
but overly conservative.

\section{Representing the \psicalculus}

\subsection{Finally tagless}

We represent the \psicalculus{} in a finally tagless manner:

\begin{code}
class (FirstOrder (Value p), HigherOrder (Value p) (Chan p)) => Psi p where
  type Chan   p :: * -> *
  type Value  p :: * -> *

  done  :: p
  new   :: DeltaQ -> (Chan p a -> p) -> p
  sync  :: SListI2 xss => POP (Chan p) xss -> (SOP (Value p) xss -> p) -> p
  out   :: Chan p a -> Value p a -> p -> p
  io    :: IO () -> p -> p
  fork  :: p -> p -> p
  fix   :: (p -> p) -> p
\end{code}

The use of finally tagless is mostly an orthogonal decision decision, but it
does work well in our current context. The |SListI2 xss| type class constraint
on |sync| is a technicality required for \texttt{generics-sop}; it will always
be satisfied. The |FirstOrder| type class encodes the operations we need on
basic values; right now, all we need is injection of the unit value, but for
more realistic examples we'll need much more here:

\begin{code}
class FirstOrder (f :: * -> *) where
  unit :: f ()
\end{code}

The |HigherOrder| type class allows us to treat channels as values:

\begin{code}
class HigherOrder (f :: * -> *) (g :: * -> *) where
  fromValue  :: f (g a) -> g a
  toValue    :: g a -> f (g a)
\end{code}

We need both of these type classes because we want to able to do \emph{abstract}
interpretation of processes, where we don't have actual values.

\subsection{Simulation}

For the concrete interpreter we instantiate

\begin{code}
type Interp = IO ()

instance Psi Interp where
  type Chan  Interp = STM.TChan
  type Value Interp = Identity
\end{code}

%if style == newcode
\begin{code}
  done       = return ()
  new _    k = STM.newTChanIO        >>= k
  sync css k = syncSTM css           >>= k
  io act   k = act                   >>  k
  out c a  k = writeTChan c a        >>  k
  fork p   k = forkIO p              >>  k
  fix        = Fun.fix

readTChan :: STM.TChan a -> (STM :.: Identity) a
readTChan c = Comp (Identity <$> STM.readTChan c)

writeTChan :: STM.TChan a -> Identity a -> IO ()
writeTChan c = STM.atomically . STM.writeTChan c . runIdentity

syncSTM :: forall xss. SListI2 xss => POP STM.TChan xss -> IO (SOP Identity xss)
syncSTM = STM.atomically
        . foldr1 STM.orElse
        . map (hsequence' . hmap readTChan)
        . apInjs_POP
\end{code}
%endif

(The details of the interpreter are not relevant for the current discussion.)
In this case the |FirstOrder| and |HigherOrder| constraints are trivially
satisfied:

\begin{code}
instance FirstOrder Identity where
  unit = Identity ()

instance HigherOrder Identity g where
  fromValue  = runIdentity
  toValue    = Identity
\end{code}

\subsection{Pretty-printer}

The pretty-printer exports a \psicalculus{} term to \LaTeX{}; it's what we've
been using throughout this document to typeset \psicalculus{} terms. We
instantiate

\begin{code}
newtype Export = Export { runExport :: Reader Int Equation }

instance Psi Export where
  type Chan  Export = K Equation
  type Value Export = K Equation
\end{code}

%if style == newcode
\begin{code}
  done       = "\\mathtt{done}"
  new _    k = Export $ do
                 c <- mkVar "c" <$> ask
                 let new' k' = "\\left(\\nu " <> c <> "\\cdot " <> k' <> "\\right)"
                 new' <$> local (+ 1) (runExport $ k (K c))
  out c a  k = Export $ do
                 let out' k' = unK c <> "!" <> unK a <> " \\parallel " <> k'
                 out' <$> runExport k
  io  _    k = k
  fork  p  k = Export $ do
                 p' <- runExport p
                 let fork' k' = p' <> " \\parallel " <> k'
                 fork' <$> runExport k
  fix      k = Export $ do
                 p <- mkVar "p" <$> ask
                 let fix' k' = "\\mathtt{rec}\\;" <> p <> "\\cdot " <> k'
                 fix' <$> local (+ 1) (runExport $ k (Export (return p)))

  sync :: forall xss. SListI2 xss
       => POP (Chan Export) xss -> (SOP (Value Export) xss -> Export) -> Export

  -- special case: single channel. This is just a direct "input"
  sync (POP ((K c :* Nil) :* Nil)) k = Export $ do
      x <- mkVar "x" <$> ask
      let sync' k' = c <> "?" <> x <> ".\\;" <> k'
      sync' <$> local (+ 1) (runExport (k (SOP (Z (K x :* Nil)))))

  -- the general case
  sync css k = Export $ do

      -- psi-calculus input prefix
      let inpPref :: (Equation, Equation) -> Equation
          inpPref (c, x) = c <> "?" <> x

      -- variable prefix for channel inputs
      x <- mkVar "x" <$> ask

      -- var used for the result of reading from the given channel
      let cvar :: Equation -> Equation
          cvar c = x <> "{}_{" <> c <> "}"

      -- the various alternatives in the case statement
      let alts :: [Alt xss]
          alts = [ (n, alt, hmap (mapKK cvar) alt)
                 | (n, alt) <- zip [0..] (apInjs_POP css)
                 ]

      -- the local channel
      c <- mkVar "c" <$> ask

      -- a forwarder reads from a set of channels, and once it has
      -- received all values, it writes a tuple to the local channel
      let forwarder :: Alt xss -> Equation
          forwarder (n, cs, xs) = mconcat [
              intercalate ".\\;" (map inpPref (zip cs' xs'))
            , ".\\;"
            , c
            , "!("
            , intercalate "," (Equation (show n) : xs')
            , ") \\\\ "
            ]
            where
              cs' = hcollapse cs
              xs' = hcollapse xs

      -- a branch from the conditional
      let branch :: Alt xss -> Reader Int Equation
          branch (n, _, xs) =
              branch' <$> local (+ 2) (runExport (k xs))
            where
              branch' k' = mconcat [
                  "\\qquad ("
                , intercalate "," (Equation (show n) : hcollapse xs)
                , ") \\rightarrow "
                , k'
                , "\\\\ "
                ]

      branches <- mapM branch alts
      return $ mconcat [
          "\\nu " <> c <> "\\cdot"
        , "\\bigparallel \\begin{pmatrix*}[l] "
        , mconcat $ map forwarder alts
        , c <> "?" <> x <> ".\\;"
        , "\\mathtt{case}\\;" <> x <> "\\;\\mathtt{of} \\\\ "
        , mconcat branches
        , "\\end{pmatrix*}"
        ]

instance IsString Export where
  fromString = Export . return . fromString

export :: Export -> Equation
export = (`runReader` 0) . runExport

-- | An alternative in the pattern match that results from a 'sync'
--
-- We record the number of the branch, the channels it reads from, and the
-- various used to hold the values read from those channels
type Alt xss = (Int, SOP (Chan Export) xss, SOP (Value Export) xss)

mkVar :: String -> Int -> Equation
mkVar pref n = fromString (pref ++ "_{" ++ show n ++ "}")
\end{code}
%endif

where |Equation| is just a wrapper around a string such that |Show|ing an
|Equation| wraps that string with the necessary \LaTeX{} magic invocations.
|Export| uses the |Reader| monad in order to be able to generate fresh
variables. The details of the pretty-printer are a bit hairy, in particular
because it needs to translate |sync| to \psicalculus{} primitives, but they are
not particular interesting. Of course, the pretty-printer \emph{is} an example
of an abstract interpreter (one that does not actually run the code) and so we
instantiate |FirstOrder| and |HigherOrder| differently:

\begin{code}
instance FirstOrder (K Equation) where
  unit = K "()"

instance HigherOrder (K Equation) (K Equation) where
  fromValue  (K str) = K str
  toValue    (K str) = K str
\end{code}

\section{The Analysis Proper}
\label{sec:Analysis}

In this section finally we represent the actual abstract interpreter, mapping
a \psicalculus{} term to its \DeltaQ{} value. First, since this is an abstract
interpretation we will not know anything about the actual values that are
being received:

\begin{code}
data AbsValue = UnknownValue

instance FirstOrder (K AbsValue) where
  unit = K UnknownValue
\end{code}

The analysis will map channels to their associated \DeltaQ{} values. This begs
the question: how do we compute the \DeltaQ{} value from a channel that we
receive (over another, higher-order, channel)? The simple answer, for now,
is: we don't:

\begin{code}
instance HigherOrder (K AbsValue) (K DeltaQ) where
  fromValue  _ = error "error: attempt to read from received channel"
  toValue    _ = K UnknownValue
\end{code}

The reason we can do this is that the only communication pattern we currently
support is where the \emph{client} creates a new channel, sends it to the
server, the server then receives that channel and only \emph{writes} to it.
Moreover, as we discussed in Section~\ref{sec:CommunicationPatterns}, the
\DeltaQ{} we associate with an \emph{output} on a channel is always |Exact 0|,
as we use asynchronous communication only. If the server \emph{did} attempt
to read from the channel it received, at that point we would need to know
its associated \DeltaQ{} value, yielding to a runtime error in the interpreter.


\begin{figure}[t]
\hrule
\begin{code}
instance Psi DeltaQ where
  type Chan   DeltaQ = K DeltaQ
  type Value  DeltaQ = K AbsValue

  done          = Exact 0
  out   _ _  k  = k
  fork  _    k  = k
  fix        k  = k (fix k)
  new   cDQ  k  = k (K cDQ)
  io    _    k  = k

  sync :: forall xss. SListI2 xss => POP (K DeltaQ) xss -> (SOP (K AbsValue) xss -> DeltaQ) -> DeltaQ
  sync css k = DepFtf $ map branch (apInjs_POP css)
    where
      branch :: SOP (K DeltaQ) xss -> (DeltaQ, DeltaQ)
      branch cs = (Ltf cDQs, k vals)
        where
          cDQs :: [DeltaQ]
          cDQs = hcollapse cs

          vals :: SOP (K AbsValue) xss
          vals = hmap (\_ -> K UnknownValue) cs
\end{code}
\hrule
\caption{\label{fig:PsiDeltaQ}Abstract interpreter computing \DeltaQ{}}
\end{figure}

The interpreter itself is now pleasantly straight-forward, and is given in
Figure~\ref{fig:PsiDeltaQ}. Hopefully there is nothing too unexpected in this
definition; |sync| in particular maps to the combination of |DepFtf| and |Lft|
that we explored in-depth in Section~\ref{sec:EmbeddingDeltaQ}. We ignore
|io| (which is primarily for debugging), and make no attempt to do something
clever for fixpoints, which will just lead to infinite \DeltaQ{} expressions.

The only surprise perhaps is the definition for |fork|, where the \DeltaQ{}
computed for |fork p q| is simply the \DeltaQ{} computed for |q|. This is
essential in the computations of \DeltaQ{} for most of the examples in
Section~\ref{sec:EmbeddingDeltaQ},  and matches a semantics where we think of
|fork| as ``spawn this auxiliary process |p|, and then continue with this main
process |q|''.

It does however of course \emph{require} that |fork| is used in this
manner. Having said that, I think it's a reasonable definition; after all,
process algebras don't have a general sequential composition operator precisely
because it doesn't really make sense to have something like
$\bigl((p \parallel q) ; r\bigr)$. Moreover, the continuation-passing style that
is used in the main Praos document can be used to enforce (or at least, strongly
encourage) this way of using |fork|, where we rely on similar restrictions to
obtain an easy semantics for broadcasting.

\section{Open Questions}

\subsection{More Intricate Communication Patterns}

In Section~\ref{sec:Analysis} we explained why we can just return |undefined|
for |fromValue| in the |HigherOrder| instantiation. This depended crucially
on the fact that we support only a single, simple, communication pattern.

This is not to say that we cannot support more intricate communication patterns.
If we need those, then the type (\DeltaQ{}) associated with the higher-order
channel must record also the type (\DeltaQ{}) associated with the channels that
we send \emph{over} those channels. In that case, we can extend |AbsValue| with
a second constructor for received channels, in which case |fromValue| can be
given a proper implementation (albeit a partial one, still, as we may still have
type incorrect processes). If we go down this route, we should probably look
at session types.

\subsection{Broadcasting}

We haven't dealt with broadcast communication explicitly, but I believe that
the exact same approach applies here also. The communication pattern we use,
where we create a local channel, send it to a server, and then wait for a
response, should apply just the same when we \emph{broadcast} that local channel.
The only difference is that when we annotate that local channel with a \DeltaQ{},
that \DeltaQ{} value should take into account the fact that it is broadcast
and that the response may come from $n$ servers (on average). It may be
convenient to introduce a combinator |FtfN NumServers DeltaQ| so that
|FtfN 5 P| is equivalent to |Ftf [P, P, P, P, P]|. If we allow for variables
in |NumServers| then the resulting \DeltaQ{} can be parameterized over how many
servers we expect to respond to a particular broadcast message.

\subsection{|FirstOrder| class members}

Currently |FirstOrder| is extremely minimal; it will need members such as

< class FirstOrder f where
<   int  :: Int -> f Int
<   add  :: f Int -> f Int -> f Int
<   eq   :: f Int -> f Int -> f Bool

etc. This can be driven by application needs.

\subsection{Choice}

The calculus does not currently have a choice construct; we will probably need
to introduce a combinator

< Psi p => choice :: Prob -> f Bool -> p -> p -> p

embedding choice within the calculus, decorated with a probability so that
we can translate this to probabilistic choice in the abstract interpreter.

\subsection{Inference}

Section~\ref{sec:manualFtf} briefly mentions that we don't do any inference
of \DeltaQ{} annotations on channels; we may be able to do slightly better here.
This may become more important if we do more to more complicated communication
patterns.

\subsection{\DeltaQ{} algebra}

The \DeltaQ{} algebra developed in Section~\ref{sec:DeltaQAlgebra} needs to
be studied and more algebraic rules need to be developed. For instance, we need
some rules that would allow us to to prove the equivalence

<     DepFtf [ ( C , D :> P ) , ( D , C :> P ) ]
< =~  C :> D :> P

mentioned in Section~\ref{sec:manualLtf2}. In particular, it would be great
if we could establish some sort of canonical form.

\bibliographystyle{acm}
\bibliography{references}

\end{document}
