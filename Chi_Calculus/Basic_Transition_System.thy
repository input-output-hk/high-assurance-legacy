section \<open>Basic Transition System\<close>

theory Basic_Transition_System
  imports Transition_Systems Processes
begin

subsection \<open>Actions\<close>

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

subsection \<open>Residuals\<close>

text \<open>
  There are two kinds of residuals in the basic transition system: acting residuals, written \<open>\<lbrace>\<alpha>\<rbrace> Q\<close>
  where \<open>\<alpha>\<close> is an action, and scope opening residuals, written \<open>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close> where \<open>a\<close> is a channel
  variable.
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
  Residual lifting is defined in the obvious way.
\<close>

inductive
  basic_lift :: "
    (('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool) \<Rightarrow>
    (('name, 'chan, 'val) basic_residual \<Rightarrow> ('name, 'chan, 'val) basic_residual \<Rightarrow> bool)"
  for \<X>
where
  acting_lift:
    "\<X> P Q \<Longrightarrow> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> P) (\<lbrace>\<alpha>\<rbrace> Q)" |
  opening_lift:
    "(\<And>a. \<X> (\<P> a) (\<Q> a)) \<Longrightarrow> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> \<P> a) (\<lbrace>\<nu> a\<rbrace> \<Q> a)"

text \<open>
  The \<^const>\<open>basic_lift\<close> operator has the properties of a residual lifting operator.
\<close>

lemma basic_lift_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> basic_lift \<X> \<le> basic_lift \<Y>"
proof
  fix C and D
  assume "basic_lift \<X> C D" and "\<X> \<le> \<Y>"
  then show "basic_lift \<Y> C D" by induction (blast intro: basic_lift.intros)+
qed
lemma basic_lift_equality_preservation: "basic_lift op = = op ="
proof (intro ext)+
  fix C\<^sub>1 and C\<^sub>2
  show "basic_lift op = C\<^sub>1 C\<^sub>2 \<longleftrightarrow> C\<^sub>1 = C\<^sub>2"
  proof
    assume "basic_lift op = C\<^sub>1 C\<^sub>2"
    then show "C\<^sub>1 = C\<^sub>2"
      by induction simp_all
  next
    assume "C\<^sub>1 = C\<^sub>2"
    then show "basic_lift op = C\<^sub>1 C\<^sub>2"
      by (induction C\<^sub>1 arbitrary: C\<^sub>2) (blast intro: basic_lift.intros)+
  qed
qed
lemma basic_lift_composition_preservation: "basic_lift (\<X> OO \<Y>) = basic_lift \<X> OO basic_lift \<Y>"
proof (intro ext)+
  fix C and E
  show "basic_lift (\<X> OO \<Y>) C E \<longleftrightarrow> (basic_lift \<X> OO basic_lift \<Y>) C E"
  proof
    assume "basic_lift (\<X> OO \<Y>) C E"
    then show "(basic_lift \<X> OO basic_lift \<Y>) C E"
    proof induction
      case (acting_lift P R \<alpha>)
      then obtain Q where "\<X> P Q" and "\<Y> Q R" by (elim relcomppE)
      then show ?case by (blast intro: basic_lift.acting_lift)
    next
      case (opening_lift \<P> \<R>)
      obtain \<Q> where "\<And>a. \<X> (\<P> a) (\<Q> a)" and "\<And>a. \<Y> (\<Q> a) (\<R> a)"
      proof -
        from `\<And>a. (\<X> OO \<Y>) (\<P> a) (\<R> a)` have "\<forall>a. \<exists>Q. \<X> (\<P> a) Q \<and> \<Y> Q (\<R> a)" by blast
        then have "\<exists>\<Q>. \<forall>a. \<X> (\<P> a) (\<Q> a) \<and> \<Y> (\<Q> a) (\<R> a)" by (fact choice)
        with that show ?thesis by blast
      qed
      then show ?case by (blast intro: basic_lift.opening_lift)
    qed
  next
    assume "(basic_lift \<X> OO basic_lift \<Y>) C E"
    then obtain D where "basic_lift \<X> C D" and "basic_lift \<Y> D E" by (elim relcomppE)
    then show "basic_lift (\<X> OO \<Y>) C E"
    proof (induction D arbitrary: C E rule: basic_residual.induct)
      case Acting
      then show ?case
        using
          basic_lift.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          relcomppI and
          basic_lift.acting_lift
        by smt
    next
      case Opening
      then show ?case
        using
          basic_lift.cases and
          basic_residual.distinct(1) and
          basic_residual.inject(2) and
          relcomppI and
          basic_lift.opening_lift
        by smt
    qed
  qed
qed
lemma basic_lift_conversion_preservation: "basic_lift \<X>\<inverse>\<inverse> = (basic_lift \<X>)\<inverse>\<inverse>"
proof (intro ext)+
  fix C and D
  show "basic_lift \<X>\<inverse>\<inverse> D C \<longleftrightarrow> (basic_lift \<X>)\<inverse>\<inverse> D C"
  proof
    assume "basic_lift \<X>\<inverse>\<inverse> D C"
    then show "(basic_lift \<X>)\<inverse>\<inverse> D C" by induction (simp_all add: basic_lift.intros)
  next
    assume "(basic_lift \<X>)\<inverse>\<inverse> D C"
    then have "basic_lift \<X> C D" by (fact conversepD)
    then show "basic_lift \<X>\<inverse>\<inverse> D C" by induction (simp_all add: basic_lift.intros)
  qed
qed

text \<open>
  Consequently, \<^type>\<open>basic_residual\<close> and \<^const>\<open>basic_lift\<close> form a residual structure.
\<close>

interpretation basic: residual basic_lift
  by
    unfold_locales
    (
      fact basic_lift_monotonicity,
      fact basic_lift_equality_preservation,
      fact basic_lift_composition_preservation,
      fact basic_lift_conversion_preservation
    )

subsection \<open>Communication\<close>

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

lemma communication_symmetry_rule [sym]: "\<eta> \<bowtie> \<mu> \<Longrightarrow> \<mu> \<bowtie> \<eta>"
  using communication.simps by metis
lemma communication_symmetry: "symp op \<bowtie>"
  using communication_symmetry_rule by (fact sympI)

subsection \<open>Transition System\<close>

text \<open>
  The following definition of the transition relation captures the set of rules that define the
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
  The residual structure and \<^const>\<open>basic_transition\<close> together form a transition system.
\<close>

interpretation basic: transition_system basic_lift basic_transition
  by unfold_locales

text \<open>
  We introduce concise notation for some of the derived predicates of the transition system.
\<close>

abbreviation
  basic_sim :: "(('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool) \<Rightarrow> bool"
  ("sim\<^sub>\<flat>")
where
  "sim\<^sub>\<flat> \<equiv> basic.sim"
abbreviation
  basic_bisim :: "(('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool) \<Rightarrow> bool"
  ("bisim\<^sub>\<flat>")
where
  "bisim\<^sub>\<flat> \<equiv> basic.bisim"
abbreviation
  basic_pre_bisimilarity :: "('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool"
  (infix "\<preceq>\<^sub>\<flat>" 50)
where
  "op \<preceq>\<^sub>\<flat> \<equiv> basic.pre_bisimilarity"
abbreviation
  basic_bisimilarity :: "('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool"
  (infix "\<sim>\<^sub>\<flat>" 50)
where
  "op \<sim>\<^sub>\<flat> \<equiv> basic.bisimilarity"

subsection \<open>Fundamental Properties of the Transition System\<close>

text \<open>
  Edsko's \texttt{Com} rule can be simulated using a combination of \<open>opening_left\<close> (or, in the
  right-to-left case, \<open>opening_right\<close>), \<open>communication\<close>, and \<open>scoped_acting\<close>. Reordering of openings
  can be simulated using \<open>scoped_opening\<close>.
\<close>

text \<open>
  An acting and an opening version of the \texttt{Scope} rule in Edsko's definition can be derived
  by combining \<open>opening\<close> with the closing rules.
\<close>

lemma acting_scope: "(\<And>a. \<Gamma> \<turnstile> \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<Q> a) \<Longrightarrow> \<Gamma> \<turnstile> \<nu> a. \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<Q> a"
  using opening by (intro scoped_acting)
lemma opening_scope: "(\<And>a. \<Gamma> \<turnstile> \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<Q> a b) \<Longrightarrow> \<Gamma> \<turnstile> \<nu> a. \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<Q> a b"
  using opening by (intro scoped_opening)

text \<open>
  No transitions are possible from~\<open>\<zero>\<close>. This is not as trivial as it might seem, because also
  \<open>scoped_acting\<close> and \<open>scoped_opening\<close> have to be taken into account.
\<close>

lemma no_basic_transitions_from_stop: "\<not> \<Gamma> \<turnstile> \<zero> \<longmapsto>\<^sub>\<flat>C"
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

subsection \<open>Bisimilarities\<close>

context begin

private lemma sim_scoped_acting_intro:
  assumes with_new_channel:
    "\<And>\<P> \<Q>. (\<And>a. \<X> (\<P> a) (\<Q> a)) \<Longrightarrow> \<X> (\<nu> a. \<P> a) (\<nu> a. \<Q> a)"
  assumes step_1:
    "\<And>T. \<X> S T \<Longrightarrow> \<exists>D\<^sub>1. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D\<^sub>1 \<and> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> \<S>\<^sub>1 a) D\<^sub>1"
  assumes step_2:
    "\<And>a T\<^sub>1. \<X> (\<S>\<^sub>1 a) T\<^sub>1 \<Longrightarrow> \<exists>D\<^sub>2. \<Gamma> \<turnstile> T\<^sub>1 \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> \<S>\<^sub>2 a) D\<^sub>2"
  assumes initial_relation:
    "\<X> S T"
  shows
    "\<exists>D\<^sub>2. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> \<nu> a. \<S>\<^sub>2 a) D\<^sub>2"
proof -
  from step_1 and `\<X> S T`
  obtain \<T>\<^sub>1 where "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and "\<And>a. \<X> (\<S>\<^sub>1 a) (\<T>\<^sub>1 a)"
    using
      basic_lift.cases and
      basic_residual.distinct(1) and
      basic_residual.inject(2)
    by (metis (full_types))
  obtain \<T>\<^sub>2 where "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a" and "\<And>a. \<X> (\<S>\<^sub>2 a) (\<T>\<^sub>2 a)"
  proof -
    from step_2 and `\<And>a. \<X> (\<S>\<^sub>1 a) (\<T>\<^sub>1 a)`
    have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> \<X> (\<S>\<^sub>2 a) H"
      using
        basic_lift.cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then have "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a \<and> \<X> (\<S>\<^sub>2 a) (\<T>\<^sub>2 a)"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
    by (fact basic_transition.scoped_acting)
  with `\<And>a. \<X> (\<S>\<^sub>2 a) (\<T>\<^sub>2 a)` show ?thesis
    using with_new_channel and acting_lift
    by blast
qed

private lemma sim_scoped_opening_intro:
  assumes with_new_channel:
    "\<And>\<P> \<Q>. (\<And>a. \<X> (\<P> a) (\<Q> a)) \<Longrightarrow> \<X> (\<nu> a. \<P> a) (\<nu> a. \<Q> a)"
  assumes step_1:
    "\<And>T. \<X> S T \<Longrightarrow> \<exists>D\<^sub>1. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D\<^sub>1 \<and> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> \<S>\<^sub>1 a) D\<^sub>1"
  assumes step_2:
    "\<And>a T\<^sub>1. \<X> (\<S>\<^sub>1 a) T\<^sub>1 \<Longrightarrow> \<exists>D\<^sub>2. \<Gamma> \<turnstile> T\<^sub>1 \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<nu> b\<rbrace> \<S>\<^sub>2 a b) D\<^sub>2"
  assumes initial_relation:
    "\<X> S T"
  shows
    "\<exists>D\<^sub>2. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<nu> b\<rbrace> \<nu> a. \<S>\<^sub>2 a b) D\<^sub>2"
proof -
  from step_1 and `\<X> S T`
  obtain \<T>\<^sub>1 where "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and "\<And>a. \<X> (\<S>\<^sub>1 a) (\<T>\<^sub>1 a)"
    using
      basic_lift.cases and
      basic_residual.distinct(1) and
      basic_residual.inject(2)
    by (metis (full_types))
  obtain \<T>\<^sub>2 where "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b" and "\<And>a b. \<X> (\<S>\<^sub>2 a b) (\<T>\<^sub>2 a b)"
  proof -
    from step_2 and `\<And>a. \<X> (\<S>\<^sub>1 a) (\<T>\<^sub>1 a)`
    have "\<forall>a. \<exists>\<H>. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. \<X> (\<S>\<^sub>2 a b) (\<H> b))"
      using
        basic_lift.cases and
        basic_residual.distinct(1) and
        basic_residual.inject(2)
      by smt
    then have "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b \<and> (\<forall>b. \<X> (\<S>\<^sub>2 a b) (\<T>\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<T>\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with `\<And>a b. \<X> (\<S>\<^sub>2 a b) (\<T>\<^sub>2 a b)` show ?thesis
    using with_new_channel and opening_lift
    by smt
qed

private method solve_sim_scoped uses with_new_channel = (
  match conclusion in
    "\<exists>D\<^sub>2. _ \<turnstile> _ \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_lift _ (\<lbrace>_\<rbrace> \<nu> a. _ a) D\<^sub>2" \<Rightarrow> \<open>
      match premises in "_ \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<S>\<^sub>1 a" for S and \<S>\<^sub>1 \<Rightarrow> \<open>
        match premises in prems [thin]: _ (multi) \<Rightarrow> \<open>
          intro sim_scoped_acting_intro [where S = S and \<S>\<^sub>1 = \<S>\<^sub>1],
          simp add: with_new_channel,
          simp_all add: prems
        \<close>
      \<close>
    \<close> \<bar>
    "\<exists>D\<^sub>2. _ \<turnstile> _ \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_lift _ (\<lbrace>\<nu> b\<rbrace> \<nu> a. _ a b) D\<^sub>2" \<Rightarrow> \<open>
      match premises in "_ \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<S>\<^sub>1 a" for S and \<S>\<^sub>1 \<Rightarrow> \<open>
        match premises in prems [thin]: _ (multi) \<Rightarrow> \<open>
          intro sim_scoped_opening_intro [where S = S and \<S>\<^sub>1 = \<S>\<^sub>1],
          simp add: with_new_channel,
          simp_all add: prems
        \<close>
      \<close>
    \<close> \<bar>
    _ \<Rightarrow> \<open>succeed\<close>
)

method basic_sim_induction for T uses with_new_channel =
  (induction arbitrary: T; solve_sim_scoped with_new_channel: with_new_channel)

end

context begin

private lemma pre_unicast_input_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x) \<Longrightarrow> c \<triangleright> x. \<P> x \<preceq>\<^sub>\<flat> c \<triangleright> x. \<Q> x"
proof (standard, intro allI, intro impI)
  assume "\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x"
  fix \<Gamma> and C
  assume "\<Gamma> \<turnstile> c \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>C"
  then show "\<exists>D. \<Gamma> \<turnstile> c \<triangleright> x. \<Q> x \<longmapsto>\<^sub>\<flat>D \<and> basic_lift op \<sim>\<^sub>\<flat> C D"
  proof cases
    case unicast_input
    with `\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x` show ?thesis
      using basic_transition.unicast_input and acting_lift
      by (metis (no_types, lifting))
  qed (simp_all add: no_opening_transitions_from_unicast_input)
qed

lemma unicast_input_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x) \<Longrightarrow> c \<triangleright> x. \<P> x \<sim>\<^sub>\<flat> c \<triangleright> x. \<Q> x"
  by (simp add: pre_unicast_input_preservation)

end

context begin

private lemma pre_broadcast_input_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x) \<Longrightarrow> \<star> \<triangleright> x. \<P> x \<preceq>\<^sub>\<flat> \<star> \<triangleright> x. \<Q> x"
proof (standard, intro allI, intro impI)
  assume "\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x"
  fix \<Gamma> and C
  assume "\<Gamma> \<turnstile> \<star> \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>C"
  then show "\<exists>D. \<Gamma> \<turnstile> \<star> \<triangleright> x. \<Q> x \<longmapsto>\<^sub>\<flat>D \<and> basic_lift op \<sim>\<^sub>\<flat> C D"
  proof cases
    case broadcast_input
    with `\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x` show ?thesis
      using basic_transition.broadcast_input and acting_lift
      by (metis (no_types, lifting))
  qed (simp_all add: no_opening_transitions_from_broadcast_input)
qed

lemma broadcast_input_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x) \<Longrightarrow> \<star> \<triangleright> x. \<P> x \<sim>\<^sub>\<flat> \<star> \<triangleright> x. \<Q> x"
  by (simp add: pre_broadcast_input_preservation)

end

context begin

private inductive
  parallel_preservation_aux :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel: "
    P \<sim>\<^sub>\<flat> Q \<Longrightarrow> parallel_preservation_aux (P \<parallel> R) (Q \<parallel> R)" |
  with_new_channel: "
    (\<And>a. parallel_preservation_aux (\<S> a) (\<T> a)) \<Longrightarrow>
    parallel_preservation_aux (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

lemma parallel_preservation: "P \<sim>\<^sub>\<flat> Q \<Longrightarrow> P \<parallel> R \<sim>\<^sub>\<flat> Q \<parallel> R"
proof (basic.bisimilarity_standard parallel_preservation_aux)
  case related
  then show ?case by (fact parallel_preservation_aux.without_new_channel)
next
  case sym
  then show ?case by induction (simp_all add: parallel_preservation_aux.intros)
next
  case (sim S T \<Gamma> C)
  then show ?case
  proof (basic_sim_induction T with_new_channel: parallel_preservation_aux.with_new_channel)
    case (communication \<eta> \<mu> P P' R R' T)
    from communication.prems show ?case
    proof cases
      case (without_new_channel Q)
      from `P \<sim>\<^sub>\<flat> Q` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'` obtain Q' where "\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> Q'" and "P' \<sim>\<^sub>\<flat> Q'"
        using 
          basic.pre_bisimilarity.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          basic_lift.cases
        by smt
      from `\<eta> \<bowtie> \<mu>` and `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> Q'` and `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> R'` have "\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q' \<parallel> R'"
        by (fact basic_transition.communication)
      with `T = Q \<parallel> R` and `P' \<sim>\<^sub>\<flat> Q'` show ?thesis
        using parallel_preservation_aux.without_new_channel and acting_lift
        by blast
    qed
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift
        by blast
    qed
  next
    case (acting_left P \<alpha> P' R T)
    from acting_left.prems show ?case
    proof cases
      case (without_new_channel Q)
      from `P \<sim>\<^sub>\<flat> Q` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P'` obtain Q' where "\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'" and "P' \<sim>\<^sub>\<flat> Q'"
        using 
          basic.pre_bisimilarity.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          basic_lift.cases
        by smt
      from `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'` have "\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<parallel> R"
        by (fact basic_transition.acting_left)
      with `T = Q \<parallel> R` and `P' \<sim>\<^sub>\<flat> Q'` show ?thesis
        using parallel_preservation_aux.without_new_channel and acting_lift
        by blast
    qed
  next
    case acting_right
    from acting_right.prems show ?case
    proof cases
      case without_new_channel
      with acting_right.hyps show ?thesis
        using
          basic_transition.acting_right and
          parallel_preservation_aux.without_new_channel and
          acting_lift
        by blast
    qed
  next
    case (opening_left P \<P> R T)
    from opening_left.prems show ?case
    proof cases
      case (without_new_channel Q)
      from `P \<sim>\<^sub>\<flat> Q` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a`
      obtain \<Q> where "\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" and "\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a"
        using 
          basic.pre_bisimilarity.cases and
          basic_residual.distinct(1) and
          basic_residual.inject(2) and
          basic_lift.cases
        by smt
      from `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a` have "\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<parallel> R"
        by (fact basic_transition.opening_left)
      with `T = Q \<parallel> R` and `\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a` show ?thesis
        using parallel_preservation_aux.without_new_channel and opening_lift
        by (metis (no_types, lifting))
    qed
  next
    case (opening_right R \<R> P T)
    from opening_right.prems show ?case
    proof cases
      case (without_new_channel Q)
      from `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<R> a` have "\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q \<parallel> \<R> a"
        by (fact basic_transition.opening_right)
      from `P \<sim>\<^sub>\<flat> Q` have "\<And>a. parallel_preservation_aux (P \<parallel> \<R> a) (Q \<parallel> \<R> a)"
        by (fact parallel_preservation_aux.without_new_channel)
      with `T = Q \<parallel> R` and `\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q \<parallel> \<R> a` show ?thesis
        using opening_lift
        by (metis (no_types, lifting))
    qed
  qed (blast elim: parallel_preservation_aux.cases)+
qed

end

context begin

private inductive
  new_channel_preservation_aux :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel: "
    P \<sim>\<^sub>\<flat> Q \<Longrightarrow> new_channel_preservation_aux P Q" |
  with_new_channel: "
    (\<And>a. new_channel_preservation_aux (\<S> a) (\<T> a)) \<Longrightarrow>
    new_channel_preservation_aux (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

private method new_channel_preservation_aux_trivial_conveyance =
  (smt
    basic.pre_bisimilarity.cases
    new_channel_preservation_aux.without_new_channel
    basic.lift_monotonicity
    predicate2I
    predicate2D)

lemma new_channel_preservation: "(\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a) \<Longrightarrow> \<nu> a. \<P> a \<sim>\<^sub>\<flat> \<nu> a. \<Q> a"
proof (basic.bisimilarity_standard new_channel_preservation_aux)
  case related
  then show ?case by (simp add: new_channel_preservation_aux.intros)
next
  case sym
  then show ?case by induction (simp_all add: new_channel_preservation_aux.intros)
next
  case (sim S T \<Gamma> C)
  from this and `\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C` show ?case
  proof (basic_sim_induction T with_new_channel: new_channel_preservation_aux.with_new_channel)
    case unicast_input
    from unicast_input.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case unicast_output
    from unicast_output.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case broadcast_input
    from broadcast_input.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case broadcast_output
    from broadcast_output.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case communication
    from communication.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift
        by blast
    qed new_channel_preservation_aux_trivial_conveyance
  next
    case invocation
    from invocation.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case acting_left
    from acting_left.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case acting_right
    from acting_right.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case opening_left
    from opening_left.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case opening_right
    from opening_right.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  qed
qed

end

context begin

private inductive
  parallel_scope_extension_subaux :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel: "
    parallel_scope_extension_subaux Q P (P \<parallel> Q)" |
  with_new_channel: "
    (\<And>a. parallel_scope_extension_subaux Q (\<P> a) (\<R> a)) \<Longrightarrow>
    parallel_scope_extension_subaux Q (\<nu> a. \<P> a) (\<nu> a. \<R> a)"

private method parallel_scope_extension_subaux_trivial_conveyance uses intro =
  (blast intro: intro parallel_scope_extension_subaux.without_new_channel)

private method parallel_scope_extension_subaux_communication_conveyance =
  (parallel_scope_extension_subaux_trivial_conveyance intro: communication)

private method parallel_scope_extension_subaux_acting_left_conveyance =
  (parallel_scope_extension_subaux_trivial_conveyance intro: acting_left)

private method parallel_scope_extension_subaux_opening_left_conveyance =
  (parallel_scope_extension_subaux_trivial_conveyance intro: opening_left)

private lemma parallel_scope_extension_subaux_opening_conveyance:
  assumes initial_relation: "parallel_scope_extension_subaux Q P T"
  assumes transition: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  shows "\<exists>\<T>. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T> a \<and> (\<forall>a. parallel_scope_extension_subaux Q (\<P> a) (\<T> a))"
using transition and initial_relation and transition
proof (induction (no_simp) P "\<lbrace>\<nu> a\<rbrace> \<P> a" arbitrary: \<P> T)
  case (opening \<P> \<P>' T)
  from opening.prems show ?case
  proof cases
    case with_new_channel
    with `\<lbrace>\<nu> a\<rbrace> \<P> a = \<lbrace>\<nu> a\<rbrace> \<P>' a` show ?thesis
      using basic_transition.opening
      by blast
  qed parallel_scope_extension_subaux_opening_left_conveyance
next
  case invocation
  from invocation.prems show ?case
    by cases parallel_scope_extension_subaux_opening_left_conveyance
next
  case opening_left
  from opening_left.prems show ?case
    by cases parallel_scope_extension_subaux_opening_left_conveyance
next
  case opening_right
  from opening_right.prems show ?case
    by cases parallel_scope_extension_subaux_opening_left_conveyance
next
  case (scoped_opening P \<P>\<^sub>1 \<P>\<^sub>2 \<P>' T)
  from
    scoped_opening.IH(1) and
    `parallel_scope_extension_subaux Q P T` and
    `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>\<^sub>1 a`
  obtain \<T>\<^sub>1 where
    "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
    "\<And>a. parallel_scope_extension_subaux Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)"
    by blast
  obtain \<T>\<^sub>2 where
    "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b" and
    "\<And>a b. parallel_scope_extension_subaux Q (\<P>\<^sub>2 a b) (\<T>\<^sub>2 a b)"
  proof -
    from
      scoped_opening.IH(2) and
      `\<And>a. parallel_scope_extension_subaux Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)` and
      `\<And>a. \<Gamma> \<turnstile> \<P>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<P>\<^sub>2 a b`
    have "
      \<forall>a. \<exists>\<H>.
      \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. parallel_scope_extension_subaux Q (\<P>\<^sub>2 a b) (\<H> b))"
      by blast
    then have "
      \<exists>\<T>\<^sub>2. \<forall>a.
      \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b \<and> (\<forall>b. parallel_scope_extension_subaux Q (\<P>\<^sub>2 a b) (\<T>\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<T>\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with
    `\<lbrace>\<nu> b\<rbrace> \<nu> a. \<P>\<^sub>2 a b = \<lbrace>\<nu> b\<rbrace> \<P>' b` and
    `\<And>a b. parallel_scope_extension_subaux Q (\<P>\<^sub>2 a b) (\<T>\<^sub>2 a b)`
  show ?case
    using basic_residual.inject(2) and parallel_scope_extension_subaux.with_new_channel
    by smt
qed simp_all

private inductive
  parallel_scope_extension_aux :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel_ltr: "
    parallel_scope_extension_subaux Q P R \<Longrightarrow> parallel_scope_extension_aux (P \<parallel> Q) R" |
  without_new_channel_rtl: "
    parallel_scope_extension_subaux Q P R \<Longrightarrow> parallel_scope_extension_aux R (P \<parallel> Q)" |
  with_new_channel: "
    (\<And>a. parallel_scope_extension_aux (\<S> a) (\<T> a)) \<Longrightarrow>
    parallel_scope_extension_aux (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

private lemma parallel_scope_extension_aux_without_new_channel_normalization:
  assumes "parallel_scope_extension_aux (P \<parallel> Q) T"
  shows "parallel_scope_extension_subaux Q P T"
using assms proof cases
  case without_new_channel_ltr
  then show ?thesis by simp
next
  case without_new_channel_rtl
  then show ?thesis
    using
      parallel_scope_extension_subaux.cases and
      parallel_scope_extension_subaux.without_new_channel
    by blast
qed

lemma parallel_scope_extension: "\<nu> a. \<P> a \<parallel> Q \<sim>\<^sub>\<flat> \<nu> a. (\<P> a \<parallel> Q)"
proof (basic.bisimilarity_standard parallel_scope_extension_aux)
  case related
  show ?case
    by (simp add:
      parallel_scope_extension_subaux.intros
      parallel_scope_extension_aux.without_new_channel_ltr)
next
  case sym
  then show ?case by induction (simp_all add: parallel_scope_extension_aux.intros)
next
  case (sim S T \<Gamma> C)
  then show ?case
  proof (basic_sim_induction T with_new_channel: parallel_scope_extension_aux.with_new_channel)
    case (communication \<eta> \<mu> P P' Q Q' T)
    from communication.prems have "parallel_scope_extension_subaux Q P T"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    from `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'` and this and communication.hyps
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T' \<and> parallel_scope_extension_subaux Q' P' T'"
    proof (induction (no_simp) P "\<lbrace>IO \<eta>\<rbrace> P'" arbitrary: P' T)
      case unicast_input
      from unicast_input.prems show ?case
        by cases parallel_scope_extension_subaux_communication_conveyance
    next
      case unicast_output
      from unicast_output.prems show ?case
        by cases parallel_scope_extension_subaux_communication_conveyance
    next
      case broadcast_input
      from broadcast_input.prems show ?case
        by cases parallel_scope_extension_subaux_communication_conveyance
    next
      case broadcast_output
      from broadcast_output.prems show ?case
        by cases parallel_scope_extension_subaux_communication_conveyance
    next
      case invocation
      from invocation.prems show ?case
        by cases parallel_scope_extension_subaux_communication_conveyance
    next
      case acting_left
      from acting_left.prems show ?case
        by cases parallel_scope_extension_subaux_communication_conveyance
    next
      case acting_right
      from acting_right.prems show ?case
        by cases parallel_scope_extension_subaux_communication_conveyance
    next
      case (scoped_acting P \<P>\<^sub>1 \<beta> \<P>\<^sub>2 P' T)
      from `\<lbrace>\<beta>\<rbrace> \<nu> a. \<P>\<^sub>2 a = \<lbrace>IO \<eta>\<rbrace> P'` have "\<beta> = IO \<eta>" and "P' = \<nu> a. \<P>\<^sub>2 a"
        by simp_all
      from `parallel_scope_extension_subaux Q P T` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>\<^sub>1 a`
      obtain \<T>\<^sub>1 where
        "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
        "\<And>a. parallel_scope_extension_subaux Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)"
        using parallel_scope_extension_subaux_opening_conveyance
        by blast
      obtain \<T>\<^sub>2 where
        "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a" and
        "\<And>a. parallel_scope_extension_subaux Q' (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)"
      proof -
        from
          `\<beta> = IO \<eta>` and
          scoped_acting.IH(2) and
          `\<And>a. parallel_scope_extension_subaux Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)` and
          `\<eta> \<bowtie> \<mu>` and
          `\<And>a. \<Gamma> \<turnstile> \<P>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<beta>\<rbrace> \<P>\<^sub>2 a` and
          `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'`
        have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> H \<and> parallel_scope_extension_subaux Q' (\<P>\<^sub>2 a) H"
          by blast
        then have
          "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a \<and> parallel_scope_extension_subaux Q' (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with `P' = \<nu> a. \<P>\<^sub>2 a` and `\<And>a. parallel_scope_extension_subaux Q' (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)`
      show ?case
        using parallel_scope_extension_subaux.with_new_channel
        by blast
    qed simp_all
    then show ?case
      using parallel_scope_extension_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (opening \<S> T)
    from opening.prems show ?case
    proof cases
      case (without_new_channel_rtl Q P)
      from `parallel_scope_extension_subaux Q P (\<nu> a. \<S> a)` show ?thesis
      proof cases
        case with_new_channel
        with `T = P \<parallel> Q` show ?thesis
          using
            basic_transition.opening and
            opening_left and
            parallel_scope_extension_aux.without_new_channel_rtl and
            opening_lift
          by (metis (mono_tags, lifting))
      qed
    next
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift
        by blast
    qed
  next
    case (acting_left P \<alpha> P' Q T)
    from acting_left.prems have "parallel_scope_extension_subaux Q P T"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    from `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P'` and this and acting_left.hyps
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' \<and> parallel_scope_extension_subaux Q P' T'"
    proof (induction (no_simp) P "\<lbrace>\<alpha>\<rbrace> P'" arbitrary: P' T)
      case unicast_input
      from unicast_input.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case unicast_output
      from unicast_output.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case broadcast_input
      from broadcast_input.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case broadcast_output
      from broadcast_output.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case communication
      from communication.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case invocation
      from invocation.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case acting_left
      from acting_left.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case acting_right
      from acting_right.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case (scoped_acting P \<P>\<^sub>1 \<beta> \<P>\<^sub>2 P' T)
      from `\<lbrace>\<beta>\<rbrace> \<nu> a. \<P>\<^sub>2 a = \<lbrace>\<alpha>\<rbrace> P'` have "\<beta> = \<alpha>" and "P' = \<nu> a. \<P>\<^sub>2 a"
        by simp_all
      from `parallel_scope_extension_subaux Q P T` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>\<^sub>1 a`
      obtain \<T>\<^sub>1 where
        "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
        "\<And>a. parallel_scope_extension_subaux Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)"
        using parallel_scope_extension_subaux_opening_conveyance
        by blast
      obtain \<T>\<^sub>2 where
        "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a" and
        "\<And>a. parallel_scope_extension_subaux Q (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)"
      proof -
        from
          `\<beta> = \<alpha>` and
          scoped_acting.IH(2) and
          `\<And>a. parallel_scope_extension_subaux Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)` and
          `\<And>a. \<Gamma> \<turnstile> \<P>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<beta>\<rbrace> \<P>\<^sub>2 a`
        have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> parallel_scope_extension_subaux Q (\<P>\<^sub>2 a) H"
          by blast
        then have
          "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a \<and> parallel_scope_extension_subaux Q (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with `P' = \<nu> a. \<P>\<^sub>2 a` and `\<And>a. parallel_scope_extension_subaux Q (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)`
      show ?case
        using parallel_scope_extension_subaux.with_new_channel
        by blast
    qed simp_all
    then show ?case
      using parallel_scope_extension_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (acting_right Q \<alpha> Q' P T)
    from acting_right.prems have "parallel_scope_extension_subaux Q P T"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    from this and acting_right.hyps
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' \<and> parallel_scope_extension_subaux Q' P T'"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.acting_right and
          parallel_scope_extension_subaux.without_new_channel
        by blast
    next
      case (with_new_channel Q \<P> \<T>)
      then have "
        \<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> parallel_scope_extension_subaux Q' (\<P> a) H"
        by simp
      then have "
        \<exists>\<T>'. \<forall>a. \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>' a \<and> parallel_scope_extension_subaux Q' (\<P> a) (\<T>' a)"
        by (fact choice)
      then show ?case
        using acting_scope and parallel_scope_extension_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using parallel_scope_extension_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (opening_left P \<P> Q T)
    from opening_left.prems have "parallel_scope_extension_subaux Q P T"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    with opening_left.hyps show ?case
      using
        parallel_scope_extension_subaux_opening_conveyance and
        parallel_scope_extension_aux.without_new_channel_ltr and
        opening_lift
      by (metis (no_types, lifting))
  next
    case (opening_right Q \<Q> P T)
    from opening_right.prems have "parallel_scope_extension_subaux Q P T"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    from this and opening_right.hyps
    have "\<exists>\<T>. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T> a \<and> (\<forall>a. parallel_scope_extension_subaux (\<Q> a) P (\<T> a))"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.opening_right and
          parallel_scope_extension_subaux.without_new_channel
        by blast
    next
      case (with_new_channel Q \<P> \<T>)
      then have "
        \<forall>a. \<exists>\<H>.
        \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. parallel_scope_extension_subaux (\<Q> b) (\<P> a) (\<H> b))"
        by simp
      then have "
        \<exists>\<T>'. \<forall>a.
        \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>' a b \<and> (\<forall>b. parallel_scope_extension_subaux (\<Q> b) (\<P> a) (\<T>' a b))"
        by (fact choice)
      then show ?case
        using opening_scope and parallel_scope_extension_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using parallel_scope_extension_aux.without_new_channel_ltr and opening_lift
      by (metis (no_types, lifting))
  qed (blast elim:
    parallel_scope_extension_subaux.cases
    parallel_scope_extension_aux.cases)+
qed

end

context begin

private lemma pre_new_channel_scope_extension: "\<nu> b. \<nu> a. \<P> a b \<preceq>\<^sub>\<flat> \<nu> a. \<nu> b. \<P> a b"
proof (standard, intro allI, intro impI)
  fix \<Gamma> and C
  assume "\<Gamma> \<turnstile> \<nu> b. \<nu> a. \<P> a b \<longmapsto>\<^sub>\<flat>C"
  then have "\<Gamma> \<turnstile> \<nu> a. \<nu> b. \<P> a b \<longmapsto>\<^sub>\<flat>C"
  proof (induction "\<nu> b. \<nu> a. \<P> a b" C)
    case opening
    show ?case using basic_transition.opening by (intro opening_scope)
  next
    case scoped_acting
    then show ?case by (simp add: basic_transition.scoped_acting)
  next
    case scoped_opening
    then show ?case by (simp add: basic_transition.scoped_opening)
  qed
  then show "\<exists>D. \<Gamma> \<turnstile> \<nu> a. \<nu> b. \<P> a b \<longmapsto>\<^sub>\<flat>D \<and> basic_lift op \<sim>\<^sub>\<flat> C D"
    using basic.bisimilarity_reflexivity and basic.lift_reflexivity_propagation and reflpD
    by smt
qed

lemma new_channel_scope_extension: "\<nu> b. \<nu> a. \<P> a b \<sim>\<^sub>\<flat> \<nu> a. \<nu> b. \<P> a b"
  by (simp add: pre_new_channel_scope_extension)

end

context begin

private inductive
  parallel_unit_aux :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel_ltr: "
    parallel_unit_aux (\<zero> \<parallel> P) P" |
  without_new_channel_rtl: "
    parallel_unit_aux P (\<zero> \<parallel> P)" |
  with_new_channel: "
    (\<And>a. parallel_unit_aux (\<S> a) (\<T> a)) \<Longrightarrow>
    parallel_unit_aux (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

private method parallel_unit_aux_trivial_conveyance =
  (blast intro:
    acting_right
    opening_right
    parallel_unit_aux.without_new_channel_rtl
    basic_lift.intros)

lemma parallel_unit: "\<zero> \<parallel> P \<sim>\<^sub>\<flat> P"
proof (basic.bisimilarity_standard parallel_unit_aux)
  case related
  show ?case by (fact parallel_unit_aux.without_new_channel_ltr)
next
  case sym
  then show ?case by induction (simp_all add: parallel_unit_aux.intros)
next
  case (sim S T \<Gamma> C)
  from this and `\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C` show ?case
  proof (basic_sim_induction T with_new_channel: parallel_unit_aux.with_new_channel)
    case unicast_input
    from unicast_input.prems show ?case
      by cases parallel_unit_aux_trivial_conveyance
  next
    case unicast_output
    from unicast_output.prems show ?case
      by cases parallel_unit_aux_trivial_conveyance
  next
    case broadcast_input
    from broadcast_input.prems show ?case
      by cases parallel_unit_aux_trivial_conveyance
  next
    case broadcast_output
    from broadcast_output.prems show ?case
      by cases parallel_unit_aux_trivial_conveyance
  next
    case communication
    from communication.prems show ?case
    proof cases
      case without_new_channel_ltr
      with communication.hyps show ?thesis
        by (simp add: no_basic_transitions_from_stop)
    qed parallel_unit_aux_trivial_conveyance
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift
        by blast
    qed parallel_unit_aux_trivial_conveyance
  next
    case (invocation N V C T)
    from invocation.prems show ?case
      by (cases, cases C) parallel_unit_aux_trivial_conveyance+
  next
    case acting_left
    from acting_left.prems show ?case
    proof cases
      case without_new_channel_ltr
      with acting_left.hyps show ?thesis
        by (simp add: no_basic_transitions_from_stop)
    qed parallel_unit_aux_trivial_conveyance
  next
    case acting_right
    from acting_right.prems show ?case
    proof cases
      case without_new_channel_ltr
      with acting_right.hyps show ?thesis
        using parallel_unit_aux.without_new_channel_ltr and acting_lift
        by blast
    qed parallel_unit_aux_trivial_conveyance
  next
    case opening_left
    from opening_left.prems show ?case
    proof cases
      case without_new_channel_ltr
      with opening_left.hyps show ?thesis
        by (simp add: no_basic_transitions_from_stop)
    qed parallel_unit_aux_trivial_conveyance
  next
    case opening_right
    from opening_right.prems show ?case
    proof cases
      case without_new_channel_ltr
      with opening_right.hyps show ?thesis
        using parallel_unit_aux.without_new_channel_ltr and opening_lift
        by metis
    qed parallel_unit_aux_trivial_conveyance
  qed
qed

end

context begin

private inductive
  nested_parallel_commutativity_subaux :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel: "
    nested_parallel_commutativity_subaux R (P \<parallel> Q) ((P \<parallel> R) \<parallel> Q)" |
  with_new_channel: "
    (\<And>a. nested_parallel_commutativity_subaux R (\<U> a) (\<T> a)) \<Longrightarrow>
    nested_parallel_commutativity_subaux R (\<nu> a. \<U> a) (\<nu> a. \<T> a)"

private lemma nested_parallel_commutativity_subaux_opening_conveyance:
  assumes initial_relation: "nested_parallel_commutativity_subaux R U T"
  assumes transition: "\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<U> a"
  shows "\<exists>\<T>. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T> a \<and> (\<forall>a. nested_parallel_commutativity_subaux R (\<U> a) (\<T> a))"
using transition and initial_relation
proof (induction U "\<lbrace>\<nu> a\<rbrace> \<U> a" arbitrary: \<U> T)
  case (opening \<U> T)
  from opening.prems show ?case
  proof cases
    case with_new_channel
    then show ?thesis
      using basic_transition.opening
      by blast
  qed
next
  case (opening_left P \<P> Q T)
  from opening_left.prems show ?case
  proof cases
    case without_new_channel
    with `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a` show ?thesis
      using
        basic_transition.opening_left and
        nested_parallel_commutativity_subaux.without_new_channel
      by blast
  qed
next
  case (opening_right Q \<Q> P T)
  from opening_right.prems show ?case
  proof cases
    case without_new_channel
    with `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a` show ?thesis
      using
        basic_transition.opening_right and
        nested_parallel_commutativity_subaux.without_new_channel
      by blast
  qed
next
  case (scoped_opening U \<U>\<^sub>1 \<U>\<^sub>2 T)
  from scoped_opening.hyps(2) and `nested_parallel_commutativity_subaux R U T`
  obtain \<T>\<^sub>1 where
    "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
    "\<And>a. nested_parallel_commutativity_subaux R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)"
    by blast
  obtain \<T>\<^sub>2 where
    "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b" and
    "\<And>a b. nested_parallel_commutativity_subaux R (\<U>\<^sub>2 a b) (\<T>\<^sub>2 a b)"
  proof -
    from scoped_opening.hyps(4) and `\<And>a. nested_parallel_commutativity_subaux R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)`
    have "
      \<forall>a. \<exists>\<H>.
      \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. nested_parallel_commutativity_subaux R (\<U>\<^sub>2 a b) (\<H> b))"
      by blast
    then have "
      \<exists>\<T>\<^sub>2. \<forall>a.
      \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b \<and> (\<forall>b. nested_parallel_commutativity_subaux R (\<U>\<^sub>2 a b) (\<T>\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<T>\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with `\<And>a b. nested_parallel_commutativity_subaux R (\<U>\<^sub>2 a b) (\<T>\<^sub>2 a b)` show ?case
    using nested_parallel_commutativity_subaux.with_new_channel
    by metis
qed (blast elim: nested_parallel_commutativity_subaux.cases)

private inductive
  nested_parallel_commutativity_aux :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel_ltr: "
    nested_parallel_commutativity_subaux R U T \<Longrightarrow>
    nested_parallel_commutativity_aux (U \<parallel> R) T" |
  without_new_channel_rtl: "
    nested_parallel_commutativity_subaux R U S \<Longrightarrow>
    nested_parallel_commutativity_aux S (U \<parallel> R)" |
  with_new_channel: "
    (\<And>a. nested_parallel_commutativity_aux (\<S> a) (\<T> a)) \<Longrightarrow>
    nested_parallel_commutativity_aux (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

private lemma nested_parallel_commutativity_aux_without_new_channel_normalization:
  assumes "nested_parallel_commutativity_aux (U \<parallel> R) T"
  shows "nested_parallel_commutativity_subaux R U T"
using assms proof cases
  case without_new_channel_ltr
  then show ?thesis by simp
next
  case without_new_channel_rtl
  then show ?thesis
    using
      nested_parallel_commutativity_subaux.cases and
      nested_parallel_commutativity_subaux.without_new_channel
    by blast
qed

private lemma nested_parallel_commutativity: "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>\<flat> (P \<parallel> R) \<parallel> Q"
proof (basic.bisimilarity_standard nested_parallel_commutativity_aux)
  case related
  show ?case
    by (simp add:
      nested_parallel_commutativity_subaux.without_new_channel
      nested_parallel_commutativity_aux.without_new_channel_ltr)
next
  case sym
  then show ?case by induction (simp_all add: nested_parallel_commutativity_aux.intros)
next
  case (sim S T \<Gamma> C)
  then show ?case
  proof (basic_sim_induction T with_new_channel: nested_parallel_commutativity_aux.with_new_channel)
    case (communication \<eta> \<mu> U U' R R' T)
    from communication.prems have "nested_parallel_commutativity_subaux R U T"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with `\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> U'`
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T' \<and> nested_parallel_commutativity_subaux R' U' T'"
    proof (induction U "\<lbrace>IO \<eta>\<rbrace> U'" arbitrary: U' T)
      case (acting_left P P' Q T)
      from acting_left.prems show ?case
      proof cases
        case without_new_channel
        with `\<eta> \<bowtie> \<mu>` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'` and `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> R'` show ?thesis
          using
            basic_transition.communication and
            basic_transition.acting_left and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_right Q Q' P T)
      from acting_right.prems show ?case
      proof cases
        case without_new_channel
        with `\<eta> \<bowtie> \<mu>` and `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> Q'` and `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> R'` show ?thesis
          using
            communication_symmetry_rule and
            basic_transition.acting_right and
            basic_transition.communication and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (scoped_acting U \<U>\<^sub>1 \<U>\<^sub>2 T)
      from `nested_parallel_commutativity_subaux R U T` and `\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<U>\<^sub>1 a`
      obtain \<T>\<^sub>1 where
        "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
        "\<And>a. nested_parallel_commutativity_subaux R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)"
        using nested_parallel_commutativity_subaux_opening_conveyance
        by blast
      obtain \<T>\<^sub>2 where
        "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a" and
        "\<And>a. nested_parallel_commutativity_subaux R' (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)"
      proof -
        from
          scoped_acting.hyps(3) and
          `\<And>a. nested_parallel_commutativity_subaux R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)`
        have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> H \<and> nested_parallel_commutativity_subaux R' (\<U>\<^sub>2 a) H"
          by blast
        then have
          "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a \<and> nested_parallel_commutativity_subaux R' (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with `\<And>a. nested_parallel_commutativity_subaux R' (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)`
      show ?case
        using nested_parallel_commutativity_subaux.with_new_channel
        by blast
    qed (blast elim: nested_parallel_commutativity_subaux.cases)+
    then show ?case
      using nested_parallel_commutativity_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (opening \<S> T)
    from opening.prems show ?case
    proof cases
      case (without_new_channel_rtl R U)
      from `nested_parallel_commutativity_subaux R U (\<nu> a. \<S> a)` show ?thesis
      proof cases
        case with_new_channel
        with `T = U \<parallel> R` show ?thesis
          using
            basic_transition.opening and
            opening_left and
            nested_parallel_commutativity_aux.without_new_channel_rtl and
            opening_lift
          by (metis (mono_tags, lifting))
      qed
    next
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift
        by blast
    qed
  next
    case (acting_left U \<alpha> U' R T)
    from acting_left.prems have "nested_parallel_commutativity_subaux R U T"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with `\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> U'`
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' \<and> nested_parallel_commutativity_subaux R U' T'"
    proof (induction U "\<lbrace>\<alpha>\<rbrace> U'" arbitrary: U' T)
      case (communication \<eta> \<mu> P P' Q Q' T)
      from communication.prems show ?case
      proof cases
        case without_new_channel
        with `\<tau> = \<alpha>` and `\<eta> \<bowtie> \<mu>` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'` and `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'` show ?thesis
          using
            basic_transition.acting_left and
            basic_transition.communication and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_left P P' Q T)
      from acting_left.prems show ?case
      proof cases
        case without_new_channel
        with `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P'` show ?thesis
          using
            basic_transition.acting_left and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_right Q Q' P T)
      from acting_right.prems show ?case
      proof cases
        case without_new_channel
        with `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'` show ?thesis
          using
            basic_transition.acting_right and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (scoped_acting U \<U>\<^sub>1 \<U>\<^sub>2 T)
      from `nested_parallel_commutativity_subaux R U T` and `\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<U>\<^sub>1 a`
      obtain \<T>\<^sub>1 where
        "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
        "\<And>a. nested_parallel_commutativity_subaux R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)"
        using nested_parallel_commutativity_subaux_opening_conveyance
        by blast
      obtain \<T>\<^sub>2 where
        "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a" and
        "\<And>a. nested_parallel_commutativity_subaux R (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)"
      proof -
        from
          scoped_acting.hyps(3) and
          `\<And>a. nested_parallel_commutativity_subaux R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)`
        have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> nested_parallel_commutativity_subaux R (\<U>\<^sub>2 a) H"
          by blast
        then have
          "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a \<and> nested_parallel_commutativity_subaux R (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with `\<And>a. nested_parallel_commutativity_subaux R (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)`
      show ?case
        using nested_parallel_commutativity_subaux.with_new_channel
        by blast
    qed (blast elim: nested_parallel_commutativity_subaux.cases)+
    then show ?case
      using nested_parallel_commutativity_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (acting_right R \<alpha> R' U T)
    from acting_right.prems have "nested_parallel_commutativity_subaux R U T"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    from this and acting_right.hyps
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' \<and> nested_parallel_commutativity_subaux R' U T'"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.acting_right and
          basic_transition.acting_left and
          nested_parallel_commutativity_subaux.without_new_channel
        by blast
    next
      case (with_new_channel R \<U> \<T>)
      then have "
        \<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> nested_parallel_commutativity_subaux R' (\<U> a) H"
        by simp
      then have "
        \<exists>\<T>'. \<forall>a. \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>' a \<and> nested_parallel_commutativity_subaux R' (\<U> a) (\<T>' a)"
        by (fact choice)
      then show ?case
        using acting_scope and nested_parallel_commutativity_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using nested_parallel_commutativity_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (opening_left U \<U> R T)
    from opening_left.prems have "nested_parallel_commutativity_subaux R U T"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with opening_left.hyps show ?case
      using
        nested_parallel_commutativity_subaux_opening_conveyance and
        nested_parallel_commutativity_aux.without_new_channel_ltr and
        opening_lift
      by (metis (no_types, lifting))
  next
    case (opening_right R \<R> U T)
    from opening_right.prems have "nested_parallel_commutativity_subaux R U T"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    from this and opening_right.hyps
    have "\<exists>\<T>. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T> a \<and> (\<forall>a. nested_parallel_commutativity_subaux (\<R> a) U (\<T> a))"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.opening_right and
          basic_transition.opening_left and
          nested_parallel_commutativity_subaux.without_new_channel
        by blast
    next
      case (with_new_channel R \<U> \<T>)
      then have "
        \<forall>a. \<exists>\<H>.
        \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. nested_parallel_commutativity_subaux (\<R> b) (\<U> a) (\<H> b))"
        by simp
      then have "
        \<exists>\<T>'. \<forall>a.
        \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>' a b \<and> (\<forall>b. nested_parallel_commutativity_subaux (\<R> b) (\<U> a) (\<T>' a b))"
        by (fact choice)
      then show ?case
        using opening_scope and nested_parallel_commutativity_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using nested_parallel_commutativity_aux.without_new_channel_ltr and opening_lift
      by (metis (no_types, lifting))
  next
  qed (blast elim:
    nested_parallel_commutativity_subaux.cases
    nested_parallel_commutativity_aux.cases)+
qed

lemma parallel_commutativity: "P \<parallel> Q \<sim>\<^sub>\<flat> Q \<parallel> P"
proof -
  have "P \<parallel> Q \<sim>\<^sub>\<flat> (\<zero> \<parallel> P) \<parallel> Q" using parallel_unit and parallel_preservation by blast
  also have "(\<zero> \<parallel> P) \<parallel> Q \<sim>\<^sub>\<flat> (\<zero> \<parallel> Q) \<parallel> P" by (fact nested_parallel_commutativity)
  also have "(\<zero> \<parallel> Q) \<parallel> P \<sim>\<^sub>\<flat> Q \<parallel> P" using parallel_unit and parallel_preservation by blast
  finally show ?thesis .
qed

lemma parallel_associativity: "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>\<flat> P \<parallel> (Q \<parallel> R)"
proof -
  have "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>\<flat> (Q \<parallel> P) \<parallel> R" using parallel_commutativity and parallel_preservation by blast
  also have "(Q \<parallel> P) \<parallel> R \<sim>\<^sub>\<flat> (Q \<parallel> R) \<parallel> P" by (fact nested_parallel_commutativity)
  also have "(Q \<parallel> R) \<parallel> P \<sim>\<^sub>\<flat> P \<parallel> (Q \<parallel> R)" by (fact parallel_commutativity)
  finally show ?thesis .
qed

end

subsection \<open>Conclusion\<close>

text \<open>
  This is all for the basic transition system.
\<close>

end
