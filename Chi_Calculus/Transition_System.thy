section \<open>Transition System\<close>

theory Transition_System
  imports Processes
begin

text \<open>
  In the $\chi$-calculus, like in the $\psi$-calculus, an output transition may open an arbitrary
  number of scopes before doing the actual output. This leads to complex rules when defining the
  transition system directly. For example, the \texttt{Com} rule in Edsko's definition does three
  things: it moves all scope openings out of the parallel composition, performs the actual
  communication, and closes all the opened scopes. Making this precise in a proof assistant is
  cumbersome. An additional complication is that the order of scope openings in a transition must
  not matter.

  Because of these difficulties, we define the transition system indirectly. First, we introduce a
  basic transition system where a transition is either an action without any scope opening or the
  opening of a single scope. The definition of this transition system consists of a clear set of
  simple rules, because each transition does only one thing. Second, we define the proper transition
  system based on the basic transition system, essentially by bundling each sequence of arbitrarily
  many scope opening transitions and a final output transition into a single transition.
\<close>

subsection \<open>Basic Transition System\<close>

text \<open>
  There are two kinds of transitions in the basic transition system: acting transitions, written
  \<open>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q\<close> where \<open>\<alpha>\<close> is an action, and scope opening transitions, written \<open>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close>
  where \<open>a\<close> is a channel variable.
\<close>

text \<open>
  Actions include various I/O actions and the silent action.
\<close>

datatype ('chan, 'val) io_action =
  UnicastIn 'chan 'val |
  UnicastOut 'chan 'val |
  BroadcastIn 'val |
  BroadcastOut 'val
datatype ('chan, 'val) basic_action =
  IO "(('chan, 'val) io_action)" |
  Silent ("\<tau>")
abbreviation UnicastInAction :: "'chan \<Rightarrow> 'val \<Rightarrow> ('chan, 'val) basic_action" ("_ \<triangleright> _") where
  "c \<triangleright> V \<equiv> IO (UnicastIn c V)"
abbreviation UnicastOutAction :: "'chan \<Rightarrow> 'val \<Rightarrow> ('chan, 'val) basic_action" ("_ \<triangleleft> _") where
  "c \<triangleleft> V \<equiv> IO (UnicastOut c V)"
abbreviation BroadcastInAction :: "'val \<Rightarrow> ('chan, 'val) basic_action" ("\<star> \<triangleright> _") where
  "\<star> \<triangleright> V \<equiv> IO (BroadcastIn V)"
abbreviation BroadcastOutAction :: "'val \<Rightarrow> ('chan, 'val) basic_action" ("\<star> \<triangleleft> _") where
  "\<star> \<triangleleft> V \<equiv> IO (BroadcastOut V)"

text \<open>
  In a transition \<open>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<phi>\<rbrace> Q\<close>, \<open>\<phi>\<close> may be of the form \<open>\<nu> a\<close> and thus bind a variable that may be
  used in~\<open>Q\<close>. Therefore, \<open>\<phi>\<close>~and~\<open>Q\<close> cannot be two separate parameters of the transition relation
  but must be bundled as a single parameter. We call such a parameter a residual, which is in line
  with the terminology used for the $\psi$-calculus. Syntactically, the part \<open>\<lbrace>\<phi>\<rbrace> Q\<close> of
  \<open>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<phi>\<rbrace> Q\<close> denotes the residual.
\<close>

datatype ('name, 'chan, 'val) basic_residual =
  Acting "(('chan, 'val) basic_action)" "(('name, 'chan, 'val) process)" ("\<lbrace>_\<rbrace> _" [0, 51] 51) |
  Opening "('chan \<Rightarrow> ('name, 'chan, 'val) process)"
syntax
  "_Opening" :: "pttrn \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) basic_residual"
  ("\<lbrace>\<nu> _\<rbrace> _" [0, 51] 51)
translations
  "\<lbrace>\<nu> a\<rbrace> P" \<rightleftharpoons> "CONST Opening (\<lambda>a. P)"

text \<open>
  There is unicast communication and broadcast communication, and communication can be from left to
  right (output on the left, input on the right) and from right to left (input on the left, output
  on the right). This results in four different ways to communicate. We do not want to have four
  communication rules, which are all analogous, and later have to handle these four rules separately
  in proofs. Therefore, we define a relation that tells which I/O action can pair with which other
  I/O action in a communication and have a single communication rule that uses this relation.
\<close>

inductive
  communication :: "
    ('chan, 'val) io_action \<Rightarrow>
    ('chan, 'val) io_action \<Rightarrow>
    bool"
  (infix "\<bowtie>" 50)
where
  unicast_ltr:
    "UnicastOut c V \<bowtie> UnicastIn c V" |
  unicast_rtl:
    "UnicastIn c V \<bowtie> UnicastOut c V" |
  broadcast_ltr:
    "BroadcastOut V \<bowtie> BroadcastIn V" |
  broadcast_rtl:
    "BroadcastIn V \<bowtie> BroadcastOut V"

text \<open>
  The communication relation is symmetric.
\<close>

lemma communication_symmetry [sym]: "\<eta> \<bowtie> \<mu> \<Longrightarrow> \<mu> \<bowtie> \<eta>"
  using communication.simps by metis

text \<open>
  A transition happens in a context that maps names to parametrized processes. We write
  \<open>\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<phi>\<rbrace> Q\<close> to say that the transition \<open>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<phi>\<rbrace> Q\<close> can take place in the context~\<open>\<Gamma>\<close>. The
  following definition of the transition relation captures the set of rules that define the
  transition system.
\<close>

inductive
  basic_transition :: "
    ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) basic_residual \<Rightarrow>
    bool"
  ("_ \<turnstile> _ \<longmapsto>\<^sub>\<flat>_" [51, 0, 51] 50)
  for \<Gamma>
where
  unicast_input:
    "\<Gamma> \<turnstile> c \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleright> V\<rbrace> \<P> V" |
  unicast_output:
    "\<Gamma> \<turnstile> c \<triangleleft> V \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft> V\<rbrace> \<zero>" |
  broadcast_input:
    "\<Gamma> \<turnstile> \<star> \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>\<lbrace>\<star> \<triangleright> V\<rbrace> \<P> V" |
  broadcast_output:
    "\<Gamma> \<turnstile> \<star> \<triangleleft> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<star> \<triangleleft> V\<rbrace> \<star> \<triangleleft> V" |
  communication:
    "\<lbrakk> \<eta> \<bowtie> \<mu>; \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'; \<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'" |
  opening:
    "\<Gamma> \<turnstile> \<nu> a. \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" |
  invocation:
    "\<Gamma> \<turnstile> \<Gamma> N V \<longmapsto>\<^sub>\<flat>C \<Longrightarrow> \<Gamma> \<turnstile> \<langle>N\<rangle> V \<longmapsto>\<^sub>\<flat>C" |
  acting_left:
    "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P' \<parallel> Q" |
  acting_right:
    "\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P \<parallel> Q'" |
  opening_left:
    "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<parallel> Q" |
  opening_right:
    "\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P \<parallel> \<Q> a" |
  scoped_acting:
    "\<lbrakk> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Gamma> \<turnstile> \<Q> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<R> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<R> a" |
  scoped_opening:
    "\<lbrakk> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Gamma> \<turnstile> \<Q> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<R> a b \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<R> a b"

text \<open>
  Note that \<open>scoped_acting\<close> and\<open>scoped_opening\<close> are the rules that perform closing.
\<close>

text \<open>
  Edsko's \texttt{Com} rule can now be simulated using a combination of \<open>opening_left\<close> (or, in the
  right-to-left case, \<open>opening_right\<close>), \<open>communication\<close>, and \<open>scoped_acting\<close>. Reordering of openings
  can be simulated using \<open>scoped_opening\<close>.
\<close>

text \<open>
  The \texttt{Scope} rule from Edsko's definition can be recovered, by combining \<open>opening\<close> with the
  closing rules.
\<close>

lemma acting_scope: "(\<And>a. \<Gamma> \<turnstile> \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<Q> a) \<Longrightarrow> \<Gamma> \<turnstile> \<nu> a. \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<Q> a"
  using opening by (intro scoped_acting)
lemma opening_scope: "(\<And>a. \<Gamma> \<turnstile> \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<Q> a b) \<Longrightarrow> \<Gamma> \<turnstile> \<nu> a. \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<Q> a b"
  using opening by (intro scoped_opening)

text \<open>
  No transitions are possible from~\<open>\<zero>\<close>. This is not as trivial as it might seem, because also
  \<open>scoped_acting\<close> and \<open>scoped_opening\<close> have to be taken into account.
\<close>

lemma no_transitions_from_stop: "\<not> \<Gamma> \<turnstile> \<zero> \<longmapsto>\<^sub>\<flat>C"
proof
  fix \<Gamma> and C :: "('name, 'chan, 'val) basic_residual"
  assume "\<Gamma> \<turnstile> \<zero> \<longmapsto>\<^sub>\<flat>C"
  then show False by (induction "\<zero> :: ('name, 'chan, 'val) process" C)
qed

text \<open>
  No opening transitions are possible from input and output processes.
\<close>

lemma no_opening_transitions_from_unicast_input: "\<not> \<Gamma> \<turnstile> c \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
proof
  assume "\<Gamma> \<turnstile> c \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then show False by (induction "c \<triangleright> x. \<P> x" "\<lbrace>\<nu> a\<rbrace> \<Q> a" arbitrary: \<Q>)
qed
lemma no_opening_transitions_from_unicast_output: "\<not> \<Gamma> \<turnstile> c \<triangleleft> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
proof
  fix \<Gamma> and c and V and \<Q> :: "'chan \<Rightarrow> ('name, 'chan, 'val) process"
  assume "\<Gamma> \<turnstile> c \<triangleleft> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then show False by (induction "c \<triangleleft> V :: ('name, 'chan, 'val) process" "\<lbrace>\<nu> a\<rbrace> \<Q> a" arbitrary: \<Q>)
qed
lemma no_opening_transitions_from_broadcast_input: "\<not> \<Gamma> \<turnstile> \<star> \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
proof
  assume "\<Gamma> \<turnstile> \<star> \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then show False by (induction "\<star> \<triangleright> x. \<P> x" "\<lbrace>\<nu> a\<rbrace> \<Q> a" arbitrary: \<Q>)
qed
lemma no_opening_transitions_from_broadcast_output: "\<not> \<Gamma> \<turnstile> \<star> \<triangleleft> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
proof
  fix \<Gamma> and V and \<Q> :: "'chan \<Rightarrow> ('name, 'chan, 'val) process"
  assume "\<Gamma> \<turnstile> \<star> \<triangleleft> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then show False by (induction "\<star> \<triangleleft> V :: ('name, 'chan, 'val) process" "\<lbrace>\<nu> a\<rbrace> \<Q> a" arbitrary: \<Q>)
qed

subsection \<open>Proper Transition System\<close>

text \<open>
  There are two kinds of transitions in the proper transition system: simple transitions, written
  \<open>P \<longmapsto>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q\<close> where \<open>\<delta>\<close> is an action, and output transitions, written
  \<open>P \<longmapsto>\<^sub>\<sharp>\<lparr>\<xi> \<triangleleft> \<nu> a\<^sub>1 \<dots> a\<^sub>n. \<V> a\<^sub>1 \<dots> a\<^sub>n\<rparr> \<Q> a\<^sub>1 \<dots> a\<^sub>n\<close> where \<open>\<xi>\<close> is either a channel or~\<open>\<star>\<close> and the \<open>a\<^sub>i\<close>
  are channel variables.
\<close>

text \<open>
  Actions include input actions and the silent action.
\<close>

datatype ('chan, 'val) action =
  UnicastIn 'chan 'val ("_ \<triangleright> _") |
  BroadcastIn 'val ("\<star> \<triangleright> _") |
  Silent ("\<tau>")

text \<open>
  Each action in the proper transition system corresponds to an action in the basic transition
  system.
\<close>

fun basic_action_of :: "('chan, 'val) action \<Rightarrow> ('chan, 'val) basic_action" where
  "basic_action_of (c \<triangleright> V) = c \<triangleright> V" |
  "basic_action_of (\<star> \<triangleright> V) = \<star> \<triangleright> V" |
  "basic_action_of \<tau> = \<tau>"

text \<open>
  A sink is the target of an output. Syntactically, the part \<open>\<xi> \<triangleleft>\<close> of an output transition
  \<open>P \<longmapsto>\<^sub>\<sharp>\<lparr>\<xi> \<triangleleft> \<nu> a\<^sub>1 \<dots> a\<^sub>n. \<V> a\<^sub>1 \<dots> a\<^sub>n\<rparr> \<Q> a\<^sub>1 \<dots> a\<^sub>n\<close> denotes the sink of the transition.
\<close>

datatype 'chan sink =
  UnicastSink 'chan ("_ \<triangleleft>") |
  BroadcastSink ("\<star> \<triangleleft>")

text \<open>
  Each pair of a sink and a value corresponds to an output action in the basic transition system.
\<close>

fun basic_output_action :: "'chan sink \<Rightarrow> 'val \<Rightarrow> ('chan, 'val) basic_action" where
  "basic_output_action (UnicastSink c) V = c \<triangleleft> V" |
  "basic_output_action BroadcastSink V = \<star> \<triangleleft> V"

text \<open>
  An output rest bundles the scope openings, the output value, and the target process of an output
  transition. Syntactically, the part \<open>\<nu> a\<^sub>1 \<dots> a\<^sub>n. \<V> a\<^sub>1 \<dots> a\<^sub>n\<rparr> \<Q> a\<^sub>1 \<dots> a\<^sub>n\<close> of an output transition
  \<open>P \<longmapsto>\<^sub>\<sharp>\<lparr>\<xi> \<triangleleft> \<nu> a\<^sub>1 \<dots> a\<^sub>n. \<V> a\<^sub>1 \<dots> a\<^sub>n\<rparr> \<Q> a\<^sub>1 \<dots> a\<^sub>n\<close> denotes the output rest of the transition.
\<close>

datatype ('name, 'chan, 'val) output_rest =
  WithoutOpening 'val "(('name, 'chan, 'val) process)" ("_\<rparr> _" [52, 51] 51) |
  WithOpening "('chan \<Rightarrow> ('name, 'chan, 'val) output_rest)" (binder "\<nu>" 51)

text \<open>
  Note that the definition of \<open>output_rest\<close> is actually more permissive than the verbal definition
  of output rests above: the number of scope openings of a particular \<open>output_rest\<close> value is not
  necessarily fixed, since the structure of a follow-up output rest in a \<open>WithOpening\<close> value can
  depend on the given channel. This is just to keep the definition simple. It does not cause any
  problems in our later proofs.
\<close>

text \<open>
  A residual bundles the label and the target process of a transition. Syntactically, the part
  \<open>\<lparr>\<psi>\<rparr> Q\<close> of a transition \<open>P \<longmapsto>\<^sub>\<sharp>\<lparr>\<psi>\<rparr> Q\<close> denotes the residual of the transition..
\<close>

datatype ('name, 'chan, 'val) residual =
  SimpleResidual "(('chan, 'val) action)" "(('name, 'chan, 'val) process)" ("\<lparr>_\<rparr> _" [0, 51] 51) |
  OutputResidual "('chan sink)" "(('name, 'chan, 'val) output_rest)" ("\<lparr>\<lfloor>_\<rfloor> \<triangleleft> _" [0, 51] 51)

text \<open>
  We use the notation \<open>\<lfloor>\<sigma>\<rfloor>\<close> to refer to the communication medium denoted by the sink~\<open>\<sigma>\<close>, which is
  a channel if \<open>\<sigma>\<close> is a unicast sink and the ether~\<open>\<star>\<close> if \<open>\<sigma>\<close> is the broadcast sink.

  Note that \<open>\<lfloor>\<sigma>\<rfloor>\<close> does not denote any first-class value. There is no type of communication mediums,
  which contains all channels and the ether. There is the \<open>sink\<close> type, which is isomorphic to such a
  hypothetical type of communication mediums. The problem with sinks is that their notation includes
  the trailing~\<open>\<triangleleft>\<close> to distinguish a channel~\<open>c\<close> from the corresponding unicast sink \<open>c \<triangleleft>\<close>. The
  \<open>\<lfloor>_\<rfloor>\<close>-construct can be thought of as stripping the~\<open>\<triangleleft>\<close> from a sink.

  We define notation for output residuals that avoids the \<open>\<lfloor>_\<rfloor>\<close>-construct for the two specific kinds
  of sinks, so that the notation with \<open>\<lfloor>_\<rfloor>\<close> is only needed when talking about arbitrary sinks.
\<close>

abbreviation
  UnicastOutResidual :: "'chan \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) residual"
  ("\<lparr>_ \<triangleleft> _\<rparr> _" [0, 0, 51] 51)
where
  "\<lparr>c \<triangleleft> V\<rparr> P \<equiv> \<lparr>\<lfloor>UnicastSink c\<rfloor> \<triangleleft> V\<rparr> P"
abbreviation
  BroadcastOutResidual :: "'val \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) residual"
  ("\<lparr>\<star> \<triangleleft> _\<rparr> _" [0, 51] 51)
where
  "\<lparr>\<star> \<triangleleft> V\<rparr> P \<equiv> \<lparr>\<lfloor>BroadcastSink\<rfloor> \<triangleleft> V\<rparr> P"

text \<open>
  A residual for broadcast input cannot be written \<open>\<lparr>\<star> \<triangleright> V\<rparr> P\<close>, since \<open>\<lparr>\<star>\<close> would be considered a
  single token.\footnote{Interestingly, \<open>\<lbrace>\<star>\<close> is not considered a single token, so that such an issue
  does not occur in the basic transition system.} As a solution, we define the desired notation for
  broadcast input residuals explicitly.
\<close>

abbreviation
  BroadcastInResidual :: "'val \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) residual"
  ("\<lparr>\<star> \<triangleright> _\<rparr> _" [0, 51] 51)
where
  "\<lparr>\<star> \<triangleright> V\<rparr> P \<equiv> \<lparr> \<star> \<triangleright> V\<rparr> P"

(* continue to write the documentation analogously to the basic transition system documentation *)

text \<open>
  We write \<open>\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<sharp>\<lparr>\<psi>\<rparr> Q\<close> to say that the transition \<open>P \<longmapsto>\<^sub>\<sharp>\<lparr>\<psi>\<rparr> Q\<close> can take place in the
  context~\<open>\<Gamma>\<close>. The following definition of the transition relation captures the set of rules that
  define the transition system.
\<close>

inductive
  transition :: "
    ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) residual \<Rightarrow>
    bool"
  ("_ \<turnstile> _ \<longmapsto>\<^sub>\<sharp>_" [51, 0, 51] 50)
  for \<Gamma>
where
  acting:
    "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" |
  output_without_opening:
    "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>basic_output_action \<sigma> V\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<sharp>\<lparr>\<lfloor>\<sigma>\<rfloor> \<triangleleft> V\<rparr> Q" |
  output_with_opening:
    "\<lbrakk> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Gamma> \<turnstile> \<Q> a \<longmapsto>\<^sub>\<sharp>\<lparr>\<lfloor>\<sigma>\<rfloor> \<triangleleft> \<K> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<sharp>\<lparr>\<lfloor>\<sigma>\<rfloor> \<triangleleft> \<nu> a. \<K> a"

subsection \<open>Discussion\<close>

text \<open>
  Our notion of broadcast differs from Edsko's in the following ways:

    \<^item> The order in which sent values are received may differ between recipients.

    \<^item> Recipients may receive a sent value arbitrarily often.

  Our transition system lets channel creation float outward further than Edsko's. For example, a
  transition \<open>(\<nu> a. c \<triangleleft> V \<parallel> a \<triangleleft> W) \<parallel> \<zero> \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> \<nu> a. (\<zero> \<parallel> a \<triangleleft> W) \<parallel> \<zero>\<close> is possible in our system,
  while Edsko’s system only allows \<open>(\<nu> a. c \<triangleleft> V \<parallel> a \<triangleleft> W) \<parallel> \<zero> \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> (\<nu> a. \<zero> \<parallel> a \<triangleleft> W) \<parallel> \<zero>\<close>. At
  the moment, we can see no problem with this change in behavior.

  The \texttt{Open} rule in Edsko's definition contains the condition $b \in n(V)$, for which there
  is no analog in our definition. Maybe this is not a problem. If it is, we might be able to fix it
  by letting \<open>unicast_open\<close> and \<open>broadcast_open\<close> additionally require that \<open>\<K>\<close> is constant.
\<close>

subsection \<open>Conclusion\<close>

text \<open>
  This is all for the transition system.
\<close>

end
