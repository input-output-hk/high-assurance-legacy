section \<open>Basic Transition System\<close>

theory Basic_Transition_System
  imports Transition_Systems.Transition_Systems Processes
begin

subsection \<open>Actions\<close>

text \<open>
  Actions include I/O actions and the silent action.
\<close>

datatype io_action =
  BasicOut chan val |
  BasicIn chan val
datatype basic_action =
  IO io_action |
  BasicSilent ("\<tau>")
abbreviation BasicOutAction :: "chan \<Rightarrow> val \<Rightarrow> basic_action" (infix "\<triangleleft>" 100) where
  "c \<triangleleft> v \<equiv> IO (BasicOut c v)"
abbreviation BasicInAction :: "chan \<Rightarrow> val \<Rightarrow> basic_action" (infix "\<triangleright>" 100) where
  "c \<triangleright> v \<equiv> IO (BasicIn c v)"

subsection \<open>Residuals\<close>

text \<open>
  There are two kinds of residuals in the basic transition system: acting residuals, written \<open>\<lbrace>\<alpha>\<rbrace> q\<close>
  where \<open>\<alpha>\<close> is an action, and scope opening residuals, written \<open>\<lbrace>\<nu> a\<rbrace> Q a\<close> where \<open>a\<close> is a channel
  variable.
\<close>

datatype basic_residual =
  Acting basic_action process ("\<lbrace>_\<rbrace> _" [0, 51] 51) |
  Opening "(chan \<Rightarrow> process)"
syntax
  "_Opening" :: "pttrn \<Rightarrow> process \<Rightarrow> basic_residual"
  ("\<lbrace>\<nu> _\<rbrace> _" [0, 51] 51)
translations
  "\<lbrace>\<nu> a\<rbrace> p" \<rightleftharpoons> "CONST Opening (\<lambda>a. p)"

text \<open>
  Residual lifting is defined in the obvious way.
\<close>

inductive
  basic_lift :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> (basic_residual \<Rightarrow> basic_residual \<Rightarrow> bool)"
  for \<X>
where
  acting_lift:
    "\<X> p q \<Longrightarrow> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> p) (\<lbrace>\<alpha>\<rbrace> q)" |
  opening_lift:
    "(\<And>a. \<X> (P a) (Q a)) \<Longrightarrow> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> Q a)"

text \<open>
  The \<^const>\<open>basic_lift\<close> operator has the properties of a residual lifting operator.
\<close>

lemma basic_lift_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> basic_lift \<X> \<le> basic_lift \<Y>"
proof
  fix d and e
  assume "basic_lift \<X> d e" and "\<X> \<le> \<Y>"
  then show "basic_lift \<Y> d e" by induction (blast intro: basic_lift.intros)+
qed
lemma basic_lift_equality_preservation: "basic_lift op = = op ="
proof (intro ext)
  fix d\<^sub>1 and d\<^sub>2
  show "basic_lift op = d\<^sub>1 d\<^sub>2 \<longleftrightarrow> d\<^sub>1 = d\<^sub>2"
  proof
    assume "basic_lift op = d\<^sub>1 d\<^sub>2"
    then show "d\<^sub>1 = d\<^sub>2"
      by induction simp_all
  next
    assume "d\<^sub>1 = d\<^sub>2"
    then show "basic_lift op = d\<^sub>1 d\<^sub>2"
      by (induction d\<^sub>1 arbitrary: d\<^sub>2) (blast intro: basic_lift.intros)+
  qed
qed
lemma basic_lift_composition_preservation: "basic_lift (\<X> OO \<Y>) = basic_lift \<X> OO basic_lift \<Y>"
proof (intro ext)
  fix d and f
  show "basic_lift (\<X> OO \<Y>) d f \<longleftrightarrow> (basic_lift \<X> OO basic_lift \<Y>) d f"
  proof
    assume "basic_lift (\<X> OO \<Y>) d f"
    then show "(basic_lift \<X> OO basic_lift \<Y>) d f"
    proof induction
      case (acting_lift p r \<alpha>)
      then obtain q where "\<X> p q" and "\<Y> q r" by (elim relcomppE)
      then show ?case by (blast intro: basic_lift.acting_lift)
    next
      case (opening_lift P R)
      obtain Q where "\<And>a. \<X> (P a) (Q a)" and "\<And>a. \<Y> (Q a) (R a)"
      proof -
        from `\<And>a. (\<X> OO \<Y>) (P a) (R a)` have "\<forall>a. \<exists>q. \<X> (P a) q \<and> \<Y> q (R a)" by blast
        then have "\<exists>Q. \<forall>a. \<X> (P a) (Q a) \<and> \<Y> (Q a) (R a)" by (fact choice)
        with that show ?thesis by blast
      qed
      then show ?case by (blast intro: basic_lift.opening_lift)
    qed
  next
    assume "(basic_lift \<X> OO basic_lift \<Y>) d f"
    then obtain e where "basic_lift \<X> d e" and "basic_lift \<Y> e f" by (elim relcomppE)
    then show "basic_lift (\<X> OO \<Y>) d f"
    proof (induction e arbitrary: d f rule: basic_residual.induct)
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
proof (intro ext)
  fix d and e
  show "basic_lift \<X>\<inverse>\<inverse> e d \<longleftrightarrow> (basic_lift \<X>)\<inverse>\<inverse> e d"
  proof
    assume "basic_lift \<X>\<inverse>\<inverse> e d"
    then show "(basic_lift \<X>)\<inverse>\<inverse> e d" by induction (simp_all add: basic_lift.intros)
  next
    assume "(basic_lift \<X>)\<inverse>\<inverse> e d"
    then have "basic_lift \<X> d e" by (fact conversepD)
    then show "basic_lift \<X>\<inverse>\<inverse> e d" by induction (simp_all add: basic_lift.intros)
  qed
qed

text \<open>
  Consequently, \<^type>\<open>basic_residual\<close> and \<^const>\<open>basic_lift\<close> form a residual structure.
\<close>

interpretation basic: residual basic_lift
  by unfold_locales (
    fact basic_lift_monotonicity,
    fact basic_lift_equality_preservation,
    fact basic_lift_composition_preservation,
    fact basic_lift_conversion_preservation
  )

subsection \<open>Communication\<close>

text \<open>
  Communication can be from left to right (output on the left, input on the right) and from right to
  left (input on the left, output on the right). We do not want to have two communication rules,
  which are analogous, and later have to handle these two rules separately in proofs. Therefore, we
  define a relation that tells which I/O action can pair with which other I/O action in a
  communication and have a single communication rule that uses this relation.
\<close>

inductive
  communication :: "io_action \<Rightarrow> io_action \<Rightarrow> bool"
  (infix "\<bowtie>" 50)
where
  ltr:
    "BasicOut c v \<bowtie> BasicIn c v" |
  rtl:
    "BasicIn c v \<bowtie> BasicOut c v"

text \<open>
  The communication relation is symmetric.
\<close>

lemma communication_symmetry_rule [sym]: "\<eta> \<bowtie> \<mu> \<Longrightarrow> \<mu> \<bowtie> \<eta>"
  using communication.simps by metis
lemma communication_symmetry: "symp op \<bowtie>"
  using communication_symmetry_rule ..

subsection \<open>Transition System\<close>

text \<open>
  The following definition of the transition relation captures the set of rules that define the
  transition system.
\<close>

inductive
  basic_transition :: "process \<Rightarrow> basic_residual \<Rightarrow> bool"
  (infix "\<longmapsto>\<^sub>\<flat>" 50)
where
  sending:
    "c \<triangleleft> v \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft> v\<rbrace> \<zero>" |
  receiving:
    "c \<triangleright> x. P x \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleright> v\<rbrace> P v" |
  communication:
    "\<lbrakk> \<eta> \<bowtie> \<mu>; p \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'; q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q' \<rbrakk> \<Longrightarrow> p \<parallel> q \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> p' \<parallel> q'" |
  opening:
    "\<nu> a. P a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a" |
  acting_left:
    "p \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p' \<Longrightarrow> p \<parallel> q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p' \<parallel> q" |
  acting_right:
    "q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q' \<Longrightarrow> p \<parallel> q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p \<parallel> q'" |
  opening_left:
    "p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<Longrightarrow> p \<parallel> q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<parallel> q" |
  opening_right:
    "q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<Longrightarrow> p \<parallel> q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> p \<parallel> Q a" |
  scoped_acting:
    "\<lbrakk> p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R a \<rbrakk> \<Longrightarrow> p \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. R a" |
  scoped_opening:
    "\<lbrakk> p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> R a b \<rbrakk> \<Longrightarrow> p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. R a b"

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
  basic_sim :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> bool"
  ("sim\<^sub>\<flat>")
where
  "sim\<^sub>\<flat> \<equiv> basic.sim"
abbreviation
  basic_bisim :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> bool"
  ("bisim\<^sub>\<flat>")
where
  "bisim\<^sub>\<flat> \<equiv> basic.bisim"
abbreviation
  basic_pre_bisimilarity :: "process \<Rightarrow> process \<Rightarrow> bool"
  (infix "\<preceq>\<^sub>\<flat>" 50)
where
  "op \<preceq>\<^sub>\<flat> \<equiv> basic.pre_bisimilarity"
abbreviation
  basic_bisimilarity :: "process \<Rightarrow> process \<Rightarrow> bool"
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

lemma acting_scope: "(\<And>a. P a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q a) \<Longrightarrow> \<nu> a. P a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. Q a"
  using opening by (intro scoped_acting)
lemma opening_scope: "(\<And>a. P a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q a b) \<Longrightarrow> \<nu> a. P a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. Q a b"
  using opening by (intro scoped_opening)

text \<open>
  No transitions are possible from~\<open>\<zero>\<close>. This is not as trivial as it might seem, because also
  \<open>scoped_acting\<close> and \<open>scoped_opening\<close> have to be taken into account.
\<close>

lemma no_basic_transitions_from_stop: "\<not> \<zero> \<longmapsto>\<^sub>\<flat>d"
proof
  fix d
  assume "\<zero> \<longmapsto>\<^sub>\<flat>d"
  then show False by (induction "\<zero>" d)
qed

text \<open>
  Only certain transitions are possible from send and receive processes.
\<close>

lemma basic_transitions_from_send: "c \<triangleleft> v \<longmapsto>\<^sub>\<flat>d \<Longrightarrow> d = \<lbrace>c \<triangleleft> v\<rbrace> \<zero>"
proof -
  fix c and v and d
  assume "c \<triangleleft> v \<longmapsto>\<^sub>\<flat>d"
  then show "d = \<lbrace>c \<triangleleft> v\<rbrace> \<zero>"
  proof (induction "c \<triangleleft> v :: process" d)
    case sending
    show ?case by (fact refl)
  next
    case scoped_acting
    then show ?case by simp
  next
    case scoped_opening
    then show ?case by simp
  qed
qed
lemma basic_transitions_from_receive:
  assumes "c \<triangleright> x. P x \<longmapsto>\<^sub>\<flat>d"
  obtains v where "d = \<lbrace>c \<triangleright> v\<rbrace> P v"
using assms proof (induction "c \<triangleright> x. P x" d)
  case receiving
  then show ?case by simp
next
  case scoped_acting
  then show ?case by blast
next
  case scoped_opening
  then show ?case by blast
qed

text \<open>
  No opening transitions are possible from send and receive processes.
\<close>

lemma no_opening_transitions_from_send: "\<not> c \<triangleleft> v \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
  using basic_transitions_from_send by fastforce
lemma no_opening_transitions_from_receive: "\<not> c \<triangleright> x. P x \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
  using basic_transitions_from_receive by fastforce

subsection \<open>Concrete Bisimilarities\<close>

context begin

private lemma sim_scoped_acting_intro:
  assumes with_new_channel:
    "\<And>P Q. (\<And>a. \<X> (P a) (Q a)) \<Longrightarrow> \<X> (\<nu> a. P a) (\<nu> a. Q a)"
  assumes step_1:
    "\<And>t. \<X> s t \<Longrightarrow> \<exists>e\<^sub>1. t \<longmapsto>\<^sub>\<flat>e\<^sub>1 \<and> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> S\<^sub>1 a) e\<^sub>1"
  assumes step_2:
    "\<And>a t\<^sub>1. \<X> (S\<^sub>1 a) t\<^sub>1 \<Longrightarrow> \<exists>e\<^sub>2. t\<^sub>1 \<longmapsto>\<^sub>\<flat>e\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> S\<^sub>2 a) e\<^sub>2"
  assumes initial_relation:
    "\<X> s t"
  shows
    "\<exists>e\<^sub>2. t \<longmapsto>\<^sub>\<flat>e\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> \<nu> a. S\<^sub>2 a) e\<^sub>2"
proof -
  from step_1 and `\<X> s t`
  obtain T\<^sub>1 where "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and "\<And>a. \<X> (S\<^sub>1 a) (T\<^sub>1 a)"
    using
      basic_lift.cases and
      basic_residual.distinct(1) and
      basic_residual.inject(2)
    by (metis (full_types))
  obtain T\<^sub>2 where "\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a" and "\<And>a. \<X> (S\<^sub>2 a) (T\<^sub>2 a)"
  proof -
    from step_2 and `\<And>a. \<X> (S\<^sub>1 a) (T\<^sub>1 a)`
    have "\<forall>a. \<exists>H. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> \<X> (S\<^sub>2 a) H"
      using
        basic_lift.cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then have "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a \<and> \<X> (S\<^sub>2 a) (T\<^sub>2 a)"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from `t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a` and `\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a` have "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. T\<^sub>2 a"
    by (fact basic_transition.scoped_acting)
  with `\<And>a. \<X> (S\<^sub>2 a) (T\<^sub>2 a)` show ?thesis
    using with_new_channel and acting_lift
    by blast
qed

private lemma sim_scoped_opening_intro:
  assumes with_new_channel:
    "\<And>P Q. (\<And>a. \<X> (P a) (Q a)) \<Longrightarrow> \<X> (\<nu> a. P a) (\<nu> a. Q a)"
  assumes step_1:
    "\<And>t. \<X> s t \<Longrightarrow> \<exists>e\<^sub>1. t \<longmapsto>\<^sub>\<flat>e\<^sub>1 \<and> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> S\<^sub>1 a) e\<^sub>1"
  assumes step_2:
    "\<And>a t\<^sub>1. \<X> (S\<^sub>1 a) t\<^sub>1 \<Longrightarrow> \<exists>e\<^sub>2. t\<^sub>1 \<longmapsto>\<^sub>\<flat>e\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<nu> b\<rbrace> S\<^sub>2 a b) e\<^sub>2"
  assumes initial_relation:
    "\<X> s t"
  shows
    "\<exists>e\<^sub>2. t \<longmapsto>\<^sub>\<flat>e\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<nu> b\<rbrace> \<nu> a. S\<^sub>2 a b) e\<^sub>2"
proof -
  from step_1 and `\<X> s t`
  obtain T\<^sub>1 where "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and "\<And>a. \<X> (S\<^sub>1 a) (T\<^sub>1 a)"
    using
      basic_lift.cases and
      basic_residual.distinct(1) and
      basic_residual.inject(2)
    by (metis (full_types))
  obtain T\<^sub>2 where "\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b" and "\<And>a b. \<X> (S\<^sub>2 a b) (T\<^sub>2 a b)"
  proof -
    from step_2 and `\<And>a. \<X> (S\<^sub>1 a) (T\<^sub>1 a)`
    have "\<forall>a. \<exists>\<H>. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. \<X> (S\<^sub>2 a b) (\<H> b))"
      using
        basic_lift.cases and
        basic_residual.distinct(1) and
        basic_residual.inject(2)
      by smt
    then have "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b \<and> (\<forall>b. \<X> (S\<^sub>2 a b) (T\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from `t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a` and `\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b` have "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. T\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with `\<And>a b. \<X> (S\<^sub>2 a b) (T\<^sub>2 a b)` show ?thesis
    using with_new_channel and opening_lift
    by smt
qed

private method solve_sim_scoped uses with_new_channel = (
  match conclusion in
    "\<exists>e\<^sub>2. _ \<longmapsto>\<^sub>\<flat>e\<^sub>2 \<and> basic_lift _ (\<lbrace>_\<rbrace> \<nu> a. _ a) e\<^sub>2" \<Rightarrow> \<open>
      match premises in "s \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> S\<^sub>1 a" for s and S\<^sub>1 \<Rightarrow> \<open>
        match premises in prems [thin]: _ (multi) \<Rightarrow> \<open>
          intro sim_scoped_acting_intro [where s = s and S\<^sub>1 = S\<^sub>1],
          simp add: with_new_channel,
          simp_all add: prems
        \<close>
      \<close>
    \<close> \<bar>
    "\<exists>e\<^sub>2. _ \<longmapsto>\<^sub>\<flat>e\<^sub>2 \<and> basic_lift _ (\<lbrace>\<nu> b\<rbrace> \<nu> a. _ a b) e\<^sub>2" \<Rightarrow> \<open>
      match premises in "s \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> S\<^sub>1 a" for s and S\<^sub>1 \<Rightarrow> \<open>
        match premises in prems [thin]: _ (multi) \<Rightarrow> \<open>
          intro sim_scoped_opening_intro [where s = s and S\<^sub>1 = S\<^sub>1],
          simp add: with_new_channel,
          simp_all add: prems
        \<close>
      \<close>
    \<close> \<bar>
    _ \<Rightarrow> \<open>succeed\<close>
)

method basic_sim_induction for t uses with_new_channel =
  (induction arbitrary: t; solve_sim_scoped with_new_channel: with_new_channel)

end

context begin

private lemma basic_pre_receive_preservation: "(\<And>x. P x \<sim>\<^sub>\<flat> Q x) \<Longrightarrow> c \<triangleright> x. P x \<preceq>\<^sub>\<flat> c \<triangleright> x. Q x"
proof (standard, intro allI, intro impI)
  assume "\<And>x. P x \<sim>\<^sub>\<flat> Q x"
  fix d
  assume "c \<triangleright> x. P x \<longmapsto>\<^sub>\<flat>d"
  then show "\<exists>e. c \<triangleright> x. Q x \<longmapsto>\<^sub>\<flat>e \<and> basic_lift op \<sim>\<^sub>\<flat> d e"
  proof cases
    case receiving
    with `\<And>x. P x \<sim>\<^sub>\<flat> Q x` show ?thesis
      using basic_transition.receiving and acting_lift
      by (metis (no_types, lifting))
  qed (simp_all add: no_opening_transitions_from_receive)
qed

lemma basic_receive_preservation: "(\<And>x. P x \<sim>\<^sub>\<flat> Q x) \<Longrightarrow> c \<triangleright> x. P x \<sim>\<^sub>\<flat> c \<triangleright> x. Q x"
  by (simp add: basic_pre_receive_preservation)

end

context begin

private inductive
  parallel_preservation_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel: "
    p \<sim>\<^sub>\<flat> q \<Longrightarrow> parallel_preservation_aux (p \<parallel> r) (q \<parallel> r)" |
  with_new_channel: "
    (\<And>a. parallel_preservation_aux (S a) (T a)) \<Longrightarrow>
    parallel_preservation_aux (\<nu> a. S a) (\<nu> a. T a)"

lemma basic_parallel_preservation: "p \<sim>\<^sub>\<flat> q \<Longrightarrow> p \<parallel> r \<sim>\<^sub>\<flat> q \<parallel> r"
proof (basic.bisimilarity_standard parallel_preservation_aux)
  case related
  then show ?case by (fact parallel_preservation_aux.without_new_channel)
next
  case sym
  then show ?case by induction (simp_all add: parallel_preservation_aux.intros)
next
  case (sim s t d)
  then show ?case
  proof (basic_sim_induction t with_new_channel: parallel_preservation_aux.with_new_channel)
    case (communication \<eta> \<mu> p p' r r' t)
    from communication.prems show ?case
    proof cases
      case (without_new_channel q)
      from `p \<sim>\<^sub>\<flat> q` and `p \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'` obtain q' where "q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
        using 
          basic.pre_bisimilarity.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          basic_lift.cases
        by smt
      from `\<eta> \<bowtie> \<mu>` and `q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> q'` and `r \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> r'` have "q \<parallel> r \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q' \<parallel> r'"
        by (fact basic_transition.communication)
      with `t = q \<parallel> r` and `p' \<sim>\<^sub>\<flat> q'` show ?thesis
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
    case (acting_left p \<alpha> p' r t)
    from acting_left.prems show ?case
    proof cases
      case (without_new_channel q)
      from `p \<sim>\<^sub>\<flat> q` and `p \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p'` obtain q' where "q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
        using 
          basic.pre_bisimilarity.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          basic_lift.cases
        by smt
      from `q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'` have "q \<parallel> r \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q' \<parallel> r"
        by (fact basic_transition.acting_left)
      with `t = q \<parallel> r` and `p' \<sim>\<^sub>\<flat> q'` show ?thesis
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
    case (opening_left p P r t)
    from opening_left.prems show ?case
    proof cases
      case (without_new_channel q)
      from `p \<sim>\<^sub>\<flat> q` and `p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a`
      obtain Q where "q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<And>a. P a \<sim>\<^sub>\<flat> Q a"
        using 
          basic.pre_bisimilarity.cases and
          basic_residual.distinct(1) and
          basic_residual.inject(2) and
          basic_lift.cases
        by smt
      from `q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a` have "q \<parallel> r \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<parallel> r"
        by (fact basic_transition.opening_left)
      with `t = q \<parallel> r` and `\<And>a. P a \<sim>\<^sub>\<flat> Q a` show ?thesis
        using parallel_preservation_aux.without_new_channel and opening_lift
        by (metis (no_types, lifting))
    qed
  next
    case (opening_right r R p t)
    from opening_right.prems show ?case
    proof cases
      case (without_new_channel q)
      from `r \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> R a` have "q \<parallel> r \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> q \<parallel> R a"
        by (fact basic_transition.opening_right)
      from `p \<sim>\<^sub>\<flat> q` have "\<And>a. parallel_preservation_aux (p \<parallel> R a) (q \<parallel> R a)"
        by (fact parallel_preservation_aux.without_new_channel)
      with `t = q \<parallel> r` and `q \<parallel> r \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> q \<parallel> R a` show ?thesis
        using opening_lift
        by (metis (no_types, lifting))
    qed
  qed (blast elim: parallel_preservation_aux.cases)+
qed

end

context begin

private inductive
  new_channel_preservation_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel: "
    p \<sim>\<^sub>\<flat> q \<Longrightarrow> new_channel_preservation_aux p q" |
  with_new_channel: "
    (\<And>a. new_channel_preservation_aux (S a) (T a)) \<Longrightarrow>
    new_channel_preservation_aux (\<nu> a. S a) (\<nu> a. T a)"

private method new_channel_preservation_aux_trivial_conveyance =
  (smt
    basic.pre_bisimilarity.cases
    new_channel_preservation_aux.without_new_channel
    basic.lift_monotonicity
    predicate2I
    predicate2D)

lemma basic_new_channel_preservation: "(\<And>a. P a \<sim>\<^sub>\<flat> Q a) \<Longrightarrow> \<nu> a. P a \<sim>\<^sub>\<flat> \<nu> a. Q a"
proof (basic.bisimilarity_standard new_channel_preservation_aux)
  case related
  then show ?case by (simp add: new_channel_preservation_aux.intros)
next
  case sym
  then show ?case by induction (simp_all add: new_channel_preservation_aux.intros)
next
  case (sim s t d)
  from this and `s \<longmapsto>\<^sub>\<flat>d` show ?case
  proof (basic_sim_induction t with_new_channel: new_channel_preservation_aux.with_new_channel)
    case sending
    from sending.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case receiving
    from receiving.prems show ?case
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
  parallel_scope_extension_subaux :: "process \<Rightarrow> process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel: "
    parallel_scope_extension_subaux q p (p \<parallel> q)" |
  with_new_channel: "
    (\<And>a. parallel_scope_extension_subaux q (P a) (R a)) \<Longrightarrow>
    parallel_scope_extension_subaux q (\<nu> a. P a) (\<nu> a. R a)"

private method parallel_scope_extension_subaux_trivial_conveyance uses intro =
  (blast intro: intro parallel_scope_extension_subaux.without_new_channel)

private method parallel_scope_extension_subaux_communication_conveyance =
  (parallel_scope_extension_subaux_trivial_conveyance intro: communication)

private method parallel_scope_extension_subaux_acting_left_conveyance =
  (parallel_scope_extension_subaux_trivial_conveyance intro: acting_left)

private method parallel_scope_extension_subaux_opening_left_conveyance =
  (parallel_scope_extension_subaux_trivial_conveyance intro: opening_left)

private lemma parallel_scope_extension_subaux_opening_conveyance:
  assumes initial_relation: "parallel_scope_extension_subaux q p t"
  assumes transition: "p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a"
  shows "\<exists>T. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T a \<and> (\<forall>a. parallel_scope_extension_subaux q (P a) (T a))"
using transition and initial_relation and transition
proof (induction (no_simp) p "\<lbrace>\<nu> a\<rbrace> P a" arbitrary: P t)
  case (opening P P' t)
  from opening.prems show ?case
  proof cases
    case with_new_channel
    with `\<lbrace>\<nu> a\<rbrace> P a = \<lbrace>\<nu> a\<rbrace> P' a` show ?thesis
      using basic_transition.opening
      by blast
  qed parallel_scope_extension_subaux_opening_left_conveyance
next
  case opening_left
  from opening_left.prems show ?case
    by cases parallel_scope_extension_subaux_opening_left_conveyance
next
  case opening_right
  from opening_right.prems show ?case
    by cases parallel_scope_extension_subaux_opening_left_conveyance
next
  case (scoped_opening p P\<^sub>1 P\<^sub>2 P' t)
  from
    scoped_opening.IH(1) and
    `parallel_scope_extension_subaux q p t` and
    `p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P\<^sub>1 a`
  obtain T\<^sub>1 where
    "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
    "\<And>a. parallel_scope_extension_subaux q (P\<^sub>1 a) (T\<^sub>1 a)"
    by blast
  obtain T\<^sub>2 where
    "\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b" and
    "\<And>a b. parallel_scope_extension_subaux q (P\<^sub>2 a b) (T\<^sub>2 a b)"
  proof -
    from
      scoped_opening.IH(2) and
      `\<And>a. parallel_scope_extension_subaux q (P\<^sub>1 a) (T\<^sub>1 a)` and
      `\<And>a. P\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P\<^sub>2 a b`
    have "
      \<forall>a. \<exists>\<H>. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. parallel_scope_extension_subaux q (P\<^sub>2 a b) (\<H> b))"
      by blast
    then have "
      \<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b \<and> (\<forall>b. parallel_scope_extension_subaux q (P\<^sub>2 a b) (T\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from `t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a` and `\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b` have "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. T\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with
    `\<lbrace>\<nu> b\<rbrace> \<nu> a. P\<^sub>2 a b = \<lbrace>\<nu> b\<rbrace> P' b` and
    `\<And>a b. parallel_scope_extension_subaux q (P\<^sub>2 a b) (T\<^sub>2 a b)`
  show ?case
    using basic_residual.inject(2) and parallel_scope_extension_subaux.with_new_channel
    by smt
qed simp_all

private inductive
  parallel_scope_extension_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel_ltr: "
    parallel_scope_extension_subaux q p r \<Longrightarrow> parallel_scope_extension_aux (p \<parallel> q) r" |
  without_new_channel_rtl: "
    parallel_scope_extension_subaux q p r \<Longrightarrow> parallel_scope_extension_aux r (p \<parallel> q)" |
  with_new_channel: "
    (\<And>a. parallel_scope_extension_aux (S a) (T a)) \<Longrightarrow>
    parallel_scope_extension_aux (\<nu> a. S a) (\<nu> a. T a)"

private lemma parallel_scope_extension_aux_without_new_channel_normalization:
  assumes "parallel_scope_extension_aux (p \<parallel> q) t"
  shows "parallel_scope_extension_subaux q p t"
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

lemma basic_parallel_scope_extension: "\<nu> a. P a \<parallel> q \<sim>\<^sub>\<flat> \<nu> a. (P a \<parallel> q)"
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
  case (sim s t d)
  then show ?case
  proof (basic_sim_induction t with_new_channel: parallel_scope_extension_aux.with_new_channel)
    case (communication \<eta> \<mu> p p' q q' t)
    from communication.prems have "parallel_scope_extension_subaux q p t"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    from `p \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'` and this and communication.hyps
    have "\<exists>t'. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> t' \<and> parallel_scope_extension_subaux q' p' t'"
    proof (induction (no_simp) p "\<lbrace>IO \<eta>\<rbrace> p'" arbitrary: p' t)
      case sending
      from sending.prems show ?case
        by cases parallel_scope_extension_subaux_communication_conveyance
    next
      case receiving
      from receiving.prems show ?case
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
      case (scoped_acting p P\<^sub>1 \<beta> P\<^sub>2 p' t)
      from `\<lbrace>\<beta>\<rbrace> \<nu> a. P\<^sub>2 a = \<lbrace>IO \<eta>\<rbrace> p'` have "\<beta> = IO \<eta>" and "p' = \<nu> a. P\<^sub>2 a"
        by simp_all
      from `parallel_scope_extension_subaux q p t` and `p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P\<^sub>1 a`
      obtain T\<^sub>1 where
        "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
        "\<And>a. parallel_scope_extension_subaux q (P\<^sub>1 a) (T\<^sub>1 a)"
        using parallel_scope_extension_subaux_opening_conveyance
        by blast
      obtain T\<^sub>2 where
        "\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a" and
        "\<And>a. parallel_scope_extension_subaux q' (P\<^sub>2 a) (T\<^sub>2 a)"
      proof -
        from
          `\<beta> = IO \<eta>` and
          scoped_acting.IH(2) and
          `\<And>a. parallel_scope_extension_subaux q (P\<^sub>1 a) (T\<^sub>1 a)` and
          `\<eta> \<bowtie> \<mu>` and
          `\<And>a. P\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<beta>\<rbrace> P\<^sub>2 a` and
          `q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q'`
        have "\<forall>a. \<exists>H. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> H \<and> parallel_scope_extension_subaux q' (P\<^sub>2 a) H"
          by blast
        then have
          "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a \<and> parallel_scope_extension_subaux q' (P\<^sub>2 a) (T\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from `t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a` and `\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a` have "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. T\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with `p' = \<nu> a. P\<^sub>2 a` and `\<And>a. parallel_scope_extension_subaux q' (P\<^sub>2 a) (T\<^sub>2 a)`
      show ?case
        using parallel_scope_extension_subaux.with_new_channel
        by blast
    qed simp_all
    then show ?case
      using parallel_scope_extension_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (opening S t)
    from opening.prems show ?case
    proof cases
      case (without_new_channel_rtl q p)
      from `parallel_scope_extension_subaux q p (\<nu> a. S a)` show ?thesis
      proof cases
        case with_new_channel
        with `t = p \<parallel> q` show ?thesis
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
    case (acting_left p \<alpha> p' q t)
    from acting_left.prems have "parallel_scope_extension_subaux q p t"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    from `p \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p'` and this and acting_left.hyps
    have "\<exists>t'. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t' \<and> parallel_scope_extension_subaux q p' t'"
    proof (induction (no_simp) p "\<lbrace>\<alpha>\<rbrace> p'" arbitrary: p' t)
      case sending
      from sending.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case receiving
      from receiving.prems show ?case
        by cases parallel_scope_extension_subaux_acting_left_conveyance
    next
      case communication
      from communication.prems show ?case
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
      case (scoped_acting p P\<^sub>1 \<beta> P\<^sub>2 p' t)
      from `\<lbrace>\<beta>\<rbrace> \<nu> a. P\<^sub>2 a = \<lbrace>\<alpha>\<rbrace> p'` have "\<beta> = \<alpha>" and "p' = \<nu> a. P\<^sub>2 a"
        by simp_all
      from `parallel_scope_extension_subaux q p t` and `p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P\<^sub>1 a`
      obtain T\<^sub>1 where
        "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
        "\<And>a. parallel_scope_extension_subaux q (P\<^sub>1 a) (T\<^sub>1 a)"
        using parallel_scope_extension_subaux_opening_conveyance
        by blast
      obtain T\<^sub>2 where
        "\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a" and
        "\<And>a. parallel_scope_extension_subaux q (P\<^sub>2 a) (T\<^sub>2 a)"
      proof -
        from
          `\<beta> = \<alpha>` and
          scoped_acting.IH(2) and
          `\<And>a. parallel_scope_extension_subaux q (P\<^sub>1 a) (T\<^sub>1 a)` and
          `\<And>a. P\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<beta>\<rbrace> P\<^sub>2 a`
        have "\<forall>a. \<exists>H. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> parallel_scope_extension_subaux q (P\<^sub>2 a) H"
          by blast
        then have
          "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a \<and> parallel_scope_extension_subaux q (P\<^sub>2 a) (T\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from `t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a` and `\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a` have "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. T\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with `p' = \<nu> a. P\<^sub>2 a` and `\<And>a. parallel_scope_extension_subaux q (P\<^sub>2 a) (T\<^sub>2 a)`
      show ?case
        using parallel_scope_extension_subaux.with_new_channel
        by blast
    qed simp_all
    then show ?case
      using parallel_scope_extension_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (acting_right q \<alpha> q' p t)
    from acting_right.prems have "parallel_scope_extension_subaux q p t"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    from this and acting_right.hyps
    have "\<exists>t'. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t' \<and> parallel_scope_extension_subaux q' p t'"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.acting_right and
          parallel_scope_extension_subaux.without_new_channel
        by blast
    next
      case (with_new_channel q P T)
      then have "
        \<forall>a. \<exists>H. T a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> parallel_scope_extension_subaux q' (P a) H"
        by simp
      then have "
        \<exists>T'. \<forall>a. T a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' a \<and> parallel_scope_extension_subaux q' (P a) (T' a)"
        by (fact choice)
      then show ?case
        using acting_scope and parallel_scope_extension_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using parallel_scope_extension_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (opening_left p P q t)
    from opening_left.prems have "parallel_scope_extension_subaux q p t"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    with opening_left.hyps show ?case
      using
        parallel_scope_extension_subaux_opening_conveyance and
        parallel_scope_extension_aux.without_new_channel_ltr and
        opening_lift
      by (metis (no_types, lifting))
  next
    case (opening_right q Q p t)
    from opening_right.prems have "parallel_scope_extension_subaux q p t"
      by (fact parallel_scope_extension_aux_without_new_channel_normalization)
    from this and opening_right.hyps
    have "\<exists>T. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T a \<and> (\<forall>a. parallel_scope_extension_subaux (Q a) p (T a))"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.opening_right and
          parallel_scope_extension_subaux.without_new_channel
        by blast
    next
      case (with_new_channel q P T)
      then have "
        \<forall>a. \<exists>\<H>. T a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. parallel_scope_extension_subaux (Q b) (P a) (\<H> b))"
        by simp
      then have "
        \<exists>T'. \<forall>a. T a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T' a b \<and> (\<forall>b. parallel_scope_extension_subaux (Q b) (P a) (T' a b))"
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

private lemma basic_pre_new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<preceq>\<^sub>\<flat> \<nu> a. \<nu> b. P a b"
proof (standard, intro allI, intro impI)
  fix d
  assume "\<nu> b. \<nu> a. P a b \<longmapsto>\<^sub>\<flat>d"
  then have "\<nu> a. \<nu> b. P a b \<longmapsto>\<^sub>\<flat>d"
  proof (induction "\<nu> b. \<nu> a. P a b" d)
    case opening
    show ?case using basic_transition.opening by (intro opening_scope)
  next
    case scoped_acting
    then show ?case by (simp add: basic_transition.scoped_acting)
  next
    case scoped_opening
    then show ?case by (simp add: basic_transition.scoped_opening)
  qed
  then show "\<exists>e. \<nu> a. \<nu> b. P a b \<longmapsto>\<^sub>\<flat>e \<and> basic_lift op \<sim>\<^sub>\<flat> d e"
    using basic.bisimilarity_reflexivity and basic.lift_reflexivity_propagation and reflpD
    by smt
qed

lemma basic_new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<sim>\<^sub>\<flat> \<nu> a. \<nu> b. P a b"
  by (simp add: basic_pre_new_channel_scope_extension)

end

context begin

private inductive
  parallel_unit_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel_ltr: "
    parallel_unit_aux (\<zero> \<parallel> p) p" |
  without_new_channel_rtl: "
    parallel_unit_aux p (\<zero> \<parallel> p)" |
  with_new_channel: "
    (\<And>a. parallel_unit_aux (S a) (T a)) \<Longrightarrow>
    parallel_unit_aux (\<nu> a. S a) (\<nu> a. T a)"

private method parallel_unit_aux_trivial_conveyance =
  (blast intro:
    acting_right
    opening_right
    parallel_unit_aux.without_new_channel_rtl
    basic_lift.intros)

lemma basic_parallel_unit: "\<zero> \<parallel> p \<sim>\<^sub>\<flat> p"
proof (basic.bisimilarity_standard parallel_unit_aux)
  case related
  show ?case by (fact parallel_unit_aux.without_new_channel_ltr)
next
  case sym
  then show ?case by induction (simp_all add: parallel_unit_aux.intros)
next
  case (sim s t d)
  from this and `s \<longmapsto>\<^sub>\<flat>d` show ?case
  proof (basic_sim_induction t with_new_channel: parallel_unit_aux.with_new_channel)
    case sending
    from sending.prems show ?case
      by cases parallel_unit_aux_trivial_conveyance
  next
    case receiving
    from receiving.prems show ?case
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
  nested_parallel_commutativity_subaux :: "process \<Rightarrow> process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel: "
    nested_parallel_commutativity_subaux r (p \<parallel> q) ((p \<parallel> r) \<parallel> q)" |
  with_new_channel: "
    (\<And>a. nested_parallel_commutativity_subaux r (U a) (T a)) \<Longrightarrow>
    nested_parallel_commutativity_subaux r (\<nu> a. U a) (\<nu> a. T a)"

private lemma nested_parallel_commutativity_subaux_opening_conveyance:
  assumes initial_relation: "nested_parallel_commutativity_subaux r u t"
  assumes transition: "u \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> U a"
  shows "\<exists>T. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T a \<and> (\<forall>a. nested_parallel_commutativity_subaux r (U a) (T a))"
using transition and initial_relation
proof (induction u "\<lbrace>\<nu> a\<rbrace> U a" arbitrary: U t)
  case (opening U t)
  from opening.prems show ?case
  proof cases
    case with_new_channel
    then show ?thesis
      using basic_transition.opening
      by blast
  qed
next
  case (opening_left p P q t)
  from opening_left.prems show ?case
  proof cases
    case without_new_channel
    with `p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a` show ?thesis
      using
        basic_transition.opening_left and
        nested_parallel_commutativity_subaux.without_new_channel
      by blast
  qed
next
  case (opening_right q Q p t)
  from opening_right.prems show ?case
  proof cases
    case without_new_channel
    with `q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a` show ?thesis
      using
        basic_transition.opening_right and
        nested_parallel_commutativity_subaux.without_new_channel
      by blast
  qed
next
  case (scoped_opening u U\<^sub>1 U\<^sub>2 t)
  from scoped_opening.hyps(2) and `nested_parallel_commutativity_subaux r u t`
  obtain T\<^sub>1 where
    "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
    "\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)"
    by blast
  obtain T\<^sub>2 where
    "\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b" and
    "\<And>a b. nested_parallel_commutativity_subaux r (U\<^sub>2 a b) (T\<^sub>2 a b)"
  proof -
    from scoped_opening.hyps(4) and `\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)`
    have "
      \<forall>a. \<exists>\<H>. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. nested_parallel_commutativity_subaux r (U\<^sub>2 a b) (\<H> b))"
      by blast
    then have "
      \<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b \<and> (\<forall>b. nested_parallel_commutativity_subaux r (U\<^sub>2 a b) (T\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from `t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a` and `\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b` have "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. T\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with `\<And>a b. nested_parallel_commutativity_subaux r (U\<^sub>2 a b) (T\<^sub>2 a b)` show ?case
    using nested_parallel_commutativity_subaux.with_new_channel
    by metis
qed

private inductive
  nested_parallel_commutativity_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel_ltr: "
    nested_parallel_commutativity_subaux r u t \<Longrightarrow>
    nested_parallel_commutativity_aux (u \<parallel> r) t" |
  without_new_channel_rtl: "
    nested_parallel_commutativity_subaux r u s \<Longrightarrow>
    nested_parallel_commutativity_aux s (u \<parallel> r)" |
  with_new_channel: "
    (\<And>a. nested_parallel_commutativity_aux (S a) (T a)) \<Longrightarrow>
    nested_parallel_commutativity_aux (\<nu> a. S a) (\<nu> a. T a)"

private lemma nested_parallel_commutativity_aux_without_new_channel_normalization:
  assumes "nested_parallel_commutativity_aux (u \<parallel> r) t"
  shows "nested_parallel_commutativity_subaux r u t"
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

private lemma basic_nested_parallel_commutativity: "(p \<parallel> q) \<parallel> r \<sim>\<^sub>\<flat> (p \<parallel> r) \<parallel> q"
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
  case (sim s t d)
  then show ?case
  proof (basic_sim_induction t with_new_channel: nested_parallel_commutativity_aux.with_new_channel)
    case (communication \<eta> \<mu> u u' r r' t)
    from communication.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with `u \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> u'`
    have "\<exists>t'. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> t' \<and> nested_parallel_commutativity_subaux r' u' t'"
    proof (induction u "\<lbrace>IO \<eta>\<rbrace> u'" arbitrary: u' t)
      case (acting_left p p' q t)
      from acting_left.prems show ?case
      proof cases
        case without_new_channel
        with `\<eta> \<bowtie> \<mu>` and `p \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'` and `r \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> r'` show ?thesis
          using
            basic_transition.communication and
            basic_transition.acting_left and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_right q q' p t)
      from acting_right.prems show ?case
      proof cases
        case without_new_channel
        with `\<eta> \<bowtie> \<mu>` and `q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> q'` and `r \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> r'` show ?thesis
          using
            communication_symmetry_rule and
            basic_transition.acting_right and
            basic_transition.communication and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (scoped_acting u U\<^sub>1 U\<^sub>2 t)
      from `nested_parallel_commutativity_subaux r u t` and `u \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> U\<^sub>1 a`
      obtain T\<^sub>1 where
        "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
        "\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)"
        using nested_parallel_commutativity_subaux_opening_conveyance
        by blast
      obtain T\<^sub>2 where
        "\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a" and
        "\<And>a. nested_parallel_commutativity_subaux r' (U\<^sub>2 a) (T\<^sub>2 a)"
      proof -
        from
          scoped_acting.hyps(3) and
          `\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)`
        have "\<forall>a. \<exists>H. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> H \<and> nested_parallel_commutativity_subaux r' (U\<^sub>2 a) H"
          by blast
        then have
          "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a \<and> nested_parallel_commutativity_subaux r' (U\<^sub>2 a) (T\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from `t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a` and `\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a` have "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. T\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with `\<And>a. nested_parallel_commutativity_subaux r' (U\<^sub>2 a) (T\<^sub>2 a)`
      show ?case
        using nested_parallel_commutativity_subaux.with_new_channel
        by blast
    qed (blast elim: nested_parallel_commutativity_subaux.cases)+
    then show ?case
      using nested_parallel_commutativity_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (opening S t)
    from opening.prems show ?case
    proof cases
      case (without_new_channel_rtl r u)
      from `nested_parallel_commutativity_subaux r u (\<nu> a. S a)` show ?thesis
      proof cases
        case with_new_channel
        with `t = u \<parallel> r` show ?thesis
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
    case (acting_left u \<alpha> u' r t)
    from acting_left.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with `u \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> u'`
    have "\<exists>t'. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t' \<and> nested_parallel_commutativity_subaux r u' t'"
    proof (induction u "\<lbrace>\<alpha>\<rbrace> u'" arbitrary: u' t)
      case (communication \<eta> \<mu> p p' q q' t)
      from communication.prems show ?case
      proof cases
        case without_new_channel
        with `\<tau> = \<alpha>` and `\<eta> \<bowtie> \<mu>` and `p \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'` and `q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q'` show ?thesis
          using
            basic_transition.acting_left and
            basic_transition.communication and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_left p p' q t)
      from acting_left.prems show ?case
      proof cases
        case without_new_channel
        with `p \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p'` show ?thesis
          using
            basic_transition.acting_left and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_right q q' p t)
      from acting_right.prems show ?case
      proof cases
        case without_new_channel
        with `q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'` show ?thesis
          using
            basic_transition.acting_right and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (scoped_acting u U\<^sub>1 U\<^sub>2 t)
      from `nested_parallel_commutativity_subaux r u t` and `u \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> U\<^sub>1 a`
      obtain T\<^sub>1 where
        "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
        "\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)"
        using nested_parallel_commutativity_subaux_opening_conveyance
        by blast
      obtain T\<^sub>2 where
        "\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a" and
        "\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>2 a) (T\<^sub>2 a)"
      proof -
        from
          scoped_acting.hyps(3) and
          `\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)`
        have "\<forall>a. \<exists>H. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> nested_parallel_commutativity_subaux r (U\<^sub>2 a) H"
          by blast
        then have
          "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a \<and> nested_parallel_commutativity_subaux r (U\<^sub>2 a) (T\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from `t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a` and `\<And>a. T\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a` have "t \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. T\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with `\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>2 a) (T\<^sub>2 a)`
      show ?case
        using nested_parallel_commutativity_subaux.with_new_channel
        by blast
    qed (blast elim: nested_parallel_commutativity_subaux.cases)+
    then show ?case
      using nested_parallel_commutativity_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (acting_right r \<alpha> r' u t)
    from acting_right.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    from this and acting_right.hyps
    have "\<exists>t'. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t' \<and> nested_parallel_commutativity_subaux r' u t'"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.acting_right and
          basic_transition.acting_left and
          nested_parallel_commutativity_subaux.without_new_channel
        by blast
    next
      case (with_new_channel r U T)
      then have "
        \<forall>a. \<exists>H. T a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> nested_parallel_commutativity_subaux r' (U a) H"
        by simp
      then have "
        \<exists>T'. \<forall>a. T a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' a \<and> nested_parallel_commutativity_subaux r' (U a) (T' a)"
        by (fact choice)
      then show ?case
        using acting_scope and nested_parallel_commutativity_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using nested_parallel_commutativity_aux.without_new_channel_ltr and acting_lift
      by blast
  next
    case (opening_left u U r t)
    from opening_left.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with opening_left.hyps show ?case
      using
        nested_parallel_commutativity_subaux_opening_conveyance and
        nested_parallel_commutativity_aux.without_new_channel_ltr and
        opening_lift
      by (metis (no_types, lifting))
  next
    case (opening_right r R u t)
    from opening_right.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    from this and opening_right.hyps
    have "\<exists>T. t \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T a \<and> (\<forall>a. nested_parallel_commutativity_subaux (R a) u (T a))"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.opening_right and
          basic_transition.opening_left and
          nested_parallel_commutativity_subaux.without_new_channel
        by blast
    next
      case (with_new_channel r U T)
      then have "
        \<forall>a. \<exists>\<H>. T a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. nested_parallel_commutativity_subaux (R b) (U a) (\<H> b))"
        by simp
      then have "
        \<exists>T'. \<forall>a.
        T a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T' a b \<and> (\<forall>b. nested_parallel_commutativity_subaux (R b) (U a) (T' a b))"
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

lemma basic_parallel_commutativity: "p \<parallel> q \<sim>\<^sub>\<flat> q \<parallel> p"
proof -
  have "p \<parallel> q \<sim>\<^sub>\<flat> (\<zero> \<parallel> p) \<parallel> q"
    using basic_parallel_unit and basic_parallel_preservation by blast
  also have "(\<zero> \<parallel> p) \<parallel> q \<sim>\<^sub>\<flat> (\<zero> \<parallel> q) \<parallel> p"
    by (fact basic_nested_parallel_commutativity)
  also have "(\<zero> \<parallel> q) \<parallel> p \<sim>\<^sub>\<flat> q \<parallel> p"
    using basic_parallel_unit and basic_parallel_preservation by blast
  finally show ?thesis .
qed

lemma basic_parallel_associativity: "(p \<parallel> q) \<parallel> r \<sim>\<^sub>\<flat> p \<parallel> (q \<parallel> r)"
proof -
  have "(p \<parallel> q) \<parallel> r \<sim>\<^sub>\<flat> (q \<parallel> p) \<parallel> r"
    using basic_parallel_commutativity and basic_parallel_preservation by blast
  also have "(q \<parallel> p) \<parallel> r \<sim>\<^sub>\<flat> (q \<parallel> r) \<parallel> p"
    by (fact basic_nested_parallel_commutativity)
  also have "(q \<parallel> r) \<parallel> p \<sim>\<^sub>\<flat> p \<parallel> (q \<parallel> r)"
    by (fact basic_parallel_commutativity)
  finally show ?thesis .
qed

end

subsection \<open>Conclusion\<close>

text \<open>
  This is all for the basic transition system.
\<close>

end
