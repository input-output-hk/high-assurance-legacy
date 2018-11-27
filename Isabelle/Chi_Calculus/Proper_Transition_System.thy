section \<open>Proper Transition System\<close>

theory Proper_Transition_System
  imports Basic_Transition_System
begin

subsection \<open>Actions\<close>

text \<open>
  Actions include input actions and the internal action.
\<close>

datatype proper_action =
  ProperIn chan val (infix "\<triangleright>" 100) |
  ProperInternal ("\<tau>")

text \<open>
  Each action in the proper transition system corresponds to an action in the basic transition
  system.
\<close>

primrec basic_action_of :: "proper_action \<Rightarrow> basic_action" where
  "basic_action_of (a \<triangleright> x) = a \<triangleright> x" |
  "basic_action_of \<tau> = \<tau>"

subsection \<open>Output Rests\<close>

text \<open>
  An output rest bundles the scope openings, the output value, and the target process of an output
  transition. Its syntax is part of the syntax of output transitions.
\<close>

datatype output_rest =
  WithoutOpening val process ("_\<rparr> _" [52, 51] 51) |
  WithOpening "(chan \<Rightarrow> output_rest)" (binder "\<nu>" 51)

text \<open>
  Note that the definition of \<open>output_rest\<close> is actually more permissive than the verbal definition
  of output rests above: the number of scope openings of a particular \<open>output_rest\<close> value is not
  necessarily fixed, since the structure of a follow-up output rest in a \<open>WithOpening\<close> value can
  depend on the given channel. This is just to keep the definition simple. It does not cause any
  problems in our later proofs.
\<close>

text \<open>
  There is a notion of output rest lifting on which the definition of residual lifting is based.
\<close>

inductive
  output_rest_lift :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> (output_rest \<Rightarrow> output_rest \<Rightarrow> bool)"
  for \<X>
where
  without_opening_lift:
    "\<X> p q \<Longrightarrow> output_rest_lift \<X> (x\<rparr> p) (x\<rparr> q)" |
  with_opening_lift:
    "(\<And>a. output_rest_lift \<X> (K a) (L a)) \<Longrightarrow> output_rest_lift \<X> (\<nu> a. K a) (\<nu> a. L a)"

text \<open>
  Interestingly, the \<^const>\<open>output_rest_lift\<close> operator has the properties of a residual lifting
  operator, despite the fact that output rests are not intended to serve as residuals but only as
  components of residuals.
\<close>

lemma output_rest_lift_monotonicity:
  "\<X> \<le> \<Y> \<Longrightarrow> output_rest_lift \<X> \<le> output_rest_lift \<Y>"
proof
  fix k and l
  assume "output_rest_lift \<X> k l" and "\<X> \<le> \<Y>"
  then show "output_rest_lift \<Y> k l" by induction (blast intro: output_rest_lift.intros)+
qed
lemma output_rest_lift_equality_preservation:
  "output_rest_lift (=) = (=)"
proof (intro ext)
  fix k\<^sub>1 and k\<^sub>2
  show "output_rest_lift (=) k\<^sub>1 k\<^sub>2 \<longleftrightarrow> k\<^sub>1 = k\<^sub>2"
  proof
    assume "output_rest_lift (=) k\<^sub>1 k\<^sub>2"
    then show "k\<^sub>1 = k\<^sub>2"
      by induction (simp_all add: ext)
  next
    assume "k\<^sub>1 = k\<^sub>2"
    then show "output_rest_lift (=) k\<^sub>1 k\<^sub>2"
      by (induction k\<^sub>1 arbitrary: k\<^sub>2) (blast intro: output_rest_lift.intros)+
  qed
qed
lemma output_rest_lift_composition_preservation:
  "output_rest_lift (\<X> OO \<Y>) = output_rest_lift \<X> OO output_rest_lift \<Y>"
proof (intro ext)
  fix k and m
  show "output_rest_lift (\<X> OO \<Y>) k m \<longleftrightarrow> (output_rest_lift \<X> OO output_rest_lift \<Y>) k m"
  proof
    assume "output_rest_lift (\<X> OO \<Y>) k m"
    then show "(output_rest_lift \<X> OO output_rest_lift \<Y>) k m"
    proof induction
      case (without_opening_lift p r x)
      then obtain q where "\<X> p q" and "\<Y> q r" by (elim relcomppE)
      then show ?case by (blast intro: output_rest_lift.without_opening_lift)
    next
      case (with_opening_lift K M)
      obtain L where "\<And>a. output_rest_lift \<X> (K a) (L a)" and "\<And>a. output_rest_lift \<Y> (L a) (M a)"
      proof -
        from `\<And>a. (output_rest_lift \<X> OO output_rest_lift \<Y>) (K a) (M a)`
        have "\<forall>a. \<exists>l. output_rest_lift \<X> (K a) l \<and> output_rest_lift \<Y> l (M a)"
          by blast
        then have "\<exists>L. \<forall>a. output_rest_lift \<X> (K a) (L a) \<and> output_rest_lift \<Y> (L a) (M a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      then show ?case by (blast intro: output_rest_lift.with_opening_lift)
    qed
  next
    assume "(output_rest_lift \<X> OO output_rest_lift \<Y>) k m"
    then obtain l where "output_rest_lift \<X> k l" and "output_rest_lift \<Y> l m" by (elim relcomppE)
    then show "output_rest_lift (\<X> OO \<Y>) k m"
    proof (induction l arbitrary: k m rule: output_rest.induct)
      case WithoutOpening
      then show ?case
        using
          output_rest_lift.cases and
          output_rest.inject(1) and
          output_rest.distinct(2) and
          relcomppI and
          output_rest_lift.without_opening_lift
        by smt
    next
      case WithOpening
      then show ?case
        using
          output_rest_lift.cases and
          output_rest.distinct(1) and
          output_rest.inject(2) and
          rangeI and
          output_rest_lift.with_opening_lift
        by smt
    qed
  qed
qed
lemma output_rest_lift_conversion_preservation:
  "output_rest_lift \<X>\<inverse>\<inverse> = (output_rest_lift \<X>)\<inverse>\<inverse>"
proof (intro ext)
  fix k and l
  show "output_rest_lift \<X>\<inverse>\<inverse> l k \<longleftrightarrow> (output_rest_lift \<X>)\<inverse>\<inverse> l k"
  proof
    assume "output_rest_lift \<X>\<inverse>\<inverse> l k"
    then show "(output_rest_lift \<X>)\<inverse>\<inverse> l k" by induction (simp_all add: output_rest_lift.intros)
  next
    assume "(output_rest_lift \<X>)\<inverse>\<inverse> l k"
    then have "output_rest_lift \<X> k l" by (fact conversepD)
    then show "output_rest_lift \<X>\<inverse>\<inverse> l k" by induction (simp_all add: output_rest_lift.intros)
  qed
qed

text \<open>
  Consequently, \<^type>\<open>output_rest\<close> and \<^const>\<open>output_rest_lift\<close> form a residual structure.
\<close>

interpretation output_rest: residual output_rest_lift
  by unfold_locales (
    fact output_rest_lift_monotonicity,
    fact output_rest_lift_equality_preservation,
    fact output_rest_lift_composition_preservation,
    fact output_rest_lift_conversion_preservation
  )

subsection \<open>Residuals\<close>

text \<open>
  There are two kinds of residuals in the proper transition system: simple residuals, written
  \<open>\<lparr>\<delta>\<rparr> q\<close> where \<open>\<delta>\<close> is an action, and output residuals, written
  \<open>\<lparr>a \<triangleleft> \<nu> b\<^sub>1 \<dots> b\<^sub>n. X b\<^sub>1 \<dots> b\<^sub>n\<rparr> Q b\<^sub>1 \<dots> b\<^sub>n\<close> where \<open>a\<close> is a channel and the \<open>b\<^sub>i\<close> are channel variables.
\<close>

datatype proper_residual =
  Simple proper_action process ("\<lparr>_\<rparr> _" [0, 51] 51) |
  Output chan output_rest ("\<lparr>_ \<triangleleft> _" [0, 51] 51)

text \<open>
  Residual lifting is defined in the obvious way.
\<close>

inductive
  proper_lift :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> (proper_residual \<Rightarrow> proper_residual \<Rightarrow> bool)"
  for \<X>
where
  simple_lift:
    "\<X> p q \<Longrightarrow> proper_lift \<X> (\<lparr>\<alpha>\<rparr> p) (\<lparr>\<alpha>\<rparr> q)" |
  output_lift:
    "output_rest_lift \<X> k l \<Longrightarrow> proper_lift \<X> (\<lparr>a \<triangleleft> k) (\<lparr>a \<triangleleft> l)"

text \<open>
  The \<^const>\<open>proper_lift\<close> operator has the properties of a residual lifting operator.
\<close>

lemma proper_lift_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> proper_lift \<X> \<le> proper_lift \<Y>"
proof
  fix c and d
  assume "proper_lift \<X> c d" and "\<X> \<le> \<Y>"
  then show "proper_lift \<Y> c d"
  proof induction
    case simple_lift
    then show ?case by (blast intro: proper_lift.simple_lift)
  next
    case output_lift
    then show ?case using output_rest_lift_monotonicity by (blast intro: proper_lift.output_lift)
  qed
qed
lemma proper_lift_equality_preservation: "proper_lift (=) = (=)"
proof (intro ext)
  fix c\<^sub>1 and c\<^sub>2
  show "proper_lift (=) c\<^sub>1 c\<^sub>2 \<longleftrightarrow> c\<^sub>1 = c\<^sub>2"
  proof
    assume "proper_lift (=) c\<^sub>1 c\<^sub>2"
    then show "c\<^sub>1 = c\<^sub>2"
      by induction (simp_all add: output_rest_lift_equality_preservation)
  next
    assume "c\<^sub>1 = c\<^sub>2"
    then show "proper_lift (=) c\<^sub>1 c\<^sub>2" by
      (induction c\<^sub>1 arbitrary: c\<^sub>2)
      (metis output_rest_lift_equality_preservation proper_lift.intros)+
  qed
qed
lemma proper_lift_composition_preservation: "proper_lift (\<X> OO \<Y>) = proper_lift \<X> OO proper_lift \<Y>"
proof (intro ext)
  fix c and e
  show "proper_lift (\<X> OO \<Y>) c e \<longleftrightarrow> (proper_lift \<X> OO proper_lift \<Y>) c e"
  proof
    assume "proper_lift (\<X> OO \<Y>) c e"
    then show "(proper_lift \<X> OO proper_lift \<Y>) c e"
    proof induction
      case (simple_lift p r \<alpha>)
      then obtain q where "\<X> p q" and "\<Y> q r" by (elim relcomppE)
      then show ?case by (blast intro: proper_lift.simple_lift)
    next
      case (output_lift k m a)
      then obtain l where "output_rest_lift \<X> k l" and "output_rest_lift \<Y> l m"
        using output_rest_lift_composition_preservation and relcomppE by metis
      then show ?case by (blast intro: proper_lift.output_lift)
    qed
  next
    assume "(proper_lift \<X> OO proper_lift \<Y>) c e"
    then obtain d where "proper_lift \<X> c d" and "proper_lift \<Y> d e" by (elim relcomppE)
    then show "proper_lift (\<X> OO \<Y>) c e"
    proof (induction d arbitrary: c e rule: proper_residual.induct)
      case Simple
      then show ?case
        using
          proper_lift.cases and
          proper_residual.inject(1) and
          proper_residual.distinct(2) and
          relcomppI and
          proper_lift.simple_lift
        by smt
    next
      case Output
      then show ?case
        using
          proper_lift.cases and
          proper_residual.distinct(1) and
          proper_residual.inject(2) and
          relcomppI and
          output_rest_lift_composition_preservation and
          proper_lift.output_lift
        by smt
    qed
  qed
qed
lemma proper_lift_conversion_preservation: "proper_lift \<X>\<inverse>\<inverse> = (proper_lift \<X>)\<inverse>\<inverse>"
proof (intro ext)
  fix c and d
  show "proper_lift \<X>\<inverse>\<inverse> d c \<longleftrightarrow> (proper_lift \<X>)\<inverse>\<inverse> d c"
  proof
    assume "proper_lift \<X>\<inverse>\<inverse> d c"
    then show "(proper_lift \<X>)\<inverse>\<inverse> d c"
      by induction (simp_all add: output_rest_lift_conversion_preservation proper_lift.intros)
  next
    assume "(proper_lift \<X>)\<inverse>\<inverse> d c"
    then have "proper_lift \<X> c d" by (fact conversepD)
    then show "proper_lift \<X>\<inverse>\<inverse> d c"
      by induction (metis conversepI output_rest_lift_conversion_preservation proper_lift.intros)+
  qed
qed

text \<open>
  Consequently, \<^type>\<open>proper_residual\<close> and \<^const>\<open>proper_lift\<close> form a residual structure.
\<close>

interpretation proper: residual proper_lift
  by unfold_locales (
    fact proper_lift_monotonicity,
    fact proper_lift_equality_preservation,
    fact proper_lift_composition_preservation,
    fact proper_lift_conversion_preservation
  )

subsection \<open>Transition System\<close>

text \<open>
  The following definition of the transition relation captures the set of rules that define the
  transition system.
\<close>

inductive
  proper_transition :: "process \<Rightarrow> proper_residual \<Rightarrow> bool"
  (infix "\<rightarrow>\<^sub>\<sharp>" 50)
where
  simple:
    "p \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" |
  output_without_opening:
    "p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q" |
  output_with_opening:
    "\<lbrakk> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b; \<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> K b \<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. K b"

text \<open>
  The residual structure and \<^const>\<open>proper_transition\<close> together form a transition system.
\<close>

interpretation proper: transition_system proper_lift proper_transition
  by intro_locales

text \<open>
  We introduce concise notation for some of the derived predicates of the transition system.
\<close>

notation proper.sim ("sim\<^sub>\<sharp>")
notation proper.bisim ("bisim\<^sub>\<sharp>")
notation proper.pre_bisimilarity (infix "\<lesssim>\<^sub>\<sharp>" 50)
notation proper.bisimilarity (infix "\<sim>\<^sub>\<sharp>" 50)

subsection \<open>Fundamental Properties of the Transition System\<close>

lemma no_proper_transitions_from_stop: "\<not> \<zero> \<rightarrow>\<^sub>\<sharp>c"
proof
  fix c
  assume "\<zero> \<rightarrow>\<^sub>\<sharp>c"
  then show False
    by (induction "\<zero>" c) (simp_all add: no_basic_transitions_from_stop)
qed

subsection \<open>Relationships between Basic and Proper Bisimilarity\<close>

lemma basic_bisimilarity_is_proper_simulation: "sim\<^sub>\<sharp> (\<sim>\<^sub>\<flat>)"
proof (intro predicate2I, intro allI, intro impI)
  fix p and q and c
  assume "p \<rightarrow>\<^sub>\<sharp>c" and "p \<sim>\<^sub>\<flat> q"
  then show "\<exists>d. q \<rightarrow>\<^sub>\<sharp>d \<and> proper_lift (\<sim>\<^sub>\<flat>) c d"
  proof (induction arbitrary: q)
    case (simple p \<delta> p' q)
    from `p \<sim>\<^sub>\<flat> q` and `p \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> p'`
    obtain q' where "q \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
      using
        basic.bisimilarity_is_simulation and
        predicate2D and
        basic_lift.cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then show ?case
      by (blast intro: proper_transition.simple simple_lift)
  next
    case (output_without_opening p a x p' q)
    from `p \<sim>\<^sub>\<flat> q` and `p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> p'`
    obtain q' where "q \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
      using
        basic.bisimilarity_is_simulation and
        predicate2D and
        basic_lift.cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then show ?case
      by (blast intro: proper_transition.output_without_opening without_opening_lift output_lift)
  next
    case (output_with_opening p P a K q)
    obtain Q where "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<And>a. P a \<sim>\<^sub>\<flat> Q a"
    proof -
      from `p \<sim>\<^sub>\<flat> q` and `p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a`
      obtain d where "q \<rightarrow>\<^sub>\<flat>d" and "basic_lift (\<sim>\<^sub>\<flat>) (\<lbrace>\<nu> a\<rbrace> P a) d"
        using basic.bisimilarity_is_simulation
        by blast
      from `basic_lift (\<sim>\<^sub>\<flat>) (\<lbrace>\<nu> a\<rbrace> P a) d` and `q \<rightarrow>\<^sub>\<flat>d` and that show ?thesis
        by cases simp
    qed
    (*
      In case we provide lemmas or proof methods for statements that we currently solve with smt,
      note that the above statement was formerly also proved using smt (after the dropping of
      contexts this surprisingly did not work anymore). Here is the old code:

          from `p \<sim>\<^sub>\<flat> q` and `p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a`
          obtain Q where "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<And>a. P a \<sim>\<^sub>\<flat> Q a"
            using
              basic.bisimilarity_is_simulation and
              predicate2D and
              basic_lift.cases and
              basic_residual.distinct(1) and
              basic_residual.inject(2)
            by smt
    *)
    obtain L where "\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b" and "\<And>b. output_rest_lift (\<sim>\<^sub>\<flat>) (K b) (L b)"
    proof -
      from output_with_opening.IH and `\<And>b. P b \<sim>\<^sub>\<flat> Q b`
      have "\<forall>b. \<exists>l. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> l \<and> output_rest_lift (\<sim>\<^sub>\<flat>) (K b) l"
        using
          proper_lift.cases and
          proper_residual.distinct(1) and
          proper_residual.inject(2)
        by smt
      then have "\<exists>L. \<forall>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b \<and> output_rest_lift (\<sim>\<^sub>\<flat>) (K b) (L b)"
        by (fact choice)
      with that show ?thesis by blast
    qed
    from `q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b` and `\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b` have "q \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. L b"
      by (fact proper_transition.output_with_opening)
    with `\<And>a. output_rest_lift (\<sim>\<^sub>\<flat>) (K a) (L a)` show ?case
      using with_opening_lift and output_lift
      by smt
  qed
qed

lemma basic_bisimilarity_is_proper_bisimulation: "bisim\<^sub>\<sharp> (\<sim>\<^sub>\<flat>)"
  using basic.bisimilarity_symmetry and basic_bisimilarity_is_proper_simulation
  by (fact proper.symmetric_simulation_is_bisimulation)

lemma basic_bisimilarity_in_proper_bisimilarity: "(\<sim>\<^sub>\<flat>) \<le> (\<sim>\<^sub>\<sharp>)"
  using basic_bisimilarity_is_proper_bisimulation
  by (fact proper.bisimulation_in_bisimilarity)

lemma basic_bisimilarity_in_proper_bisimilarity_rule: "p \<sim>\<^sub>\<flat> q \<Longrightarrow> p \<sim>\<^sub>\<sharp> q"
  using basic_bisimilarity_in_proper_bisimilarity ..

subsection \<open>Concrete Bisimilarities\<close>

lemma proper_receive_preservation: "(\<And>x. P x \<sim>\<^sub>\<sharp> Q x) \<Longrightarrow> a \<triangleright> x. P x \<sim>\<^sub>\<sharp> a \<triangleright> x. Q x"
  sorry

lemma proper_parallel_preservation: "p \<sim>\<^sub>\<sharp> q \<Longrightarrow> p \<parallel> r \<sim>\<^sub>\<sharp> q \<parallel> r"
  sorry

lemma proper_new_channel_preservation: "(\<And>a. P a \<sim>\<^sub>\<sharp> Q a) \<Longrightarrow> \<nu> a. P a \<sim>\<^sub>\<sharp> \<nu> a. Q a"
  sorry

context begin

private lemma proper_pre_receive_scope_extension_ltr: "a \<triangleright> x. \<nu> b. P x b \<lesssim>\<^sub>\<sharp> \<nu> b. a \<triangleright> x. P x b"
proof (standard, intro allI, intro impI)
  fix c
  assume "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>c"
  then show "\<exists>d. \<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>d \<and> proper_lift (\<sim>\<^sub>\<sharp>) c d"
  proof cases
    case (simple \<delta> q)
    from `a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q`
    obtain x where "basic_action_of \<delta> = a \<triangleright> x" and "q = \<nu> b. P x b"
      by (blast elim: basic_transitions_from_receive)
    from `basic_action_of \<delta> = a \<triangleright> x` have "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> b. P x b"
      using receiving and acting_scope
      by smt
    with `c = \<lparr>\<delta>\<rparr> q` and `q = \<nu> b. P x b` have "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>c"
      by (blast intro: proper_transition.simple)
    then show ?thesis
      using proper.bisimilarity_reflexivity and proper.lift_reflexivity_propagation and reflpD
      by smt
  next
    case (output_without_opening a x q)
    then show ?thesis
      using basic_transitions_from_receive
      by fastforce
  next
    case output_with_opening
    then show ?thesis by (simp add: no_opening_transitions_from_receive)
  qed
qed

private lemma opening_transitions_from_new_channel_receive:
  "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b \<Longrightarrow> Q b = a \<triangleright> x . P x b"
proof (induction "\<nu> b. a \<triangleright> x. P x b" "\<lbrace>\<nu> b\<rbrace> Q b" arbitrary: Q rule: basic_transition.induct)
  case opening
  show ?case by (fact refl)
next
  case scoped_opening
  then show ?case using no_opening_transitions_from_receive by metis
qed

private lemma proper_pre_receive_scope_extension_rtl: "\<nu> b. a \<triangleright> x. P x b \<lesssim>\<^sub>\<sharp> a \<triangleright> x. \<nu> b. P x b"
proof (standard, intro allI, intro impI)
  fix c
  assume "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>c"
  then show "\<exists>d. a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>d \<and> proper_lift (\<sim>\<^sub>\<sharp>) c d"
  proof cases
    case (simple \<delta> r)
    from `\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> r` show ?thesis
    proof cases
      case (scoped_acting Q R)
      from `\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b` have "\<And>b. Q b = a \<triangleright> x . P x b"
        by (fact opening_transitions_from_new_channel_receive)
      with `\<And>b. Q b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> R b`
      obtain x where "basic_action_of \<delta> = a \<triangleright> x" and "\<And>b. R b = P x b"
        using
          basic_transitions_from_receive and
          basic_residual.inject(1) and
          basic_action.inject(1) and
          io_action.inject(2)
        by smt
      from `basic_action_of \<delta> = a \<triangleright> x` have "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> b. P x b"
        using receiving
        by fastforce
      moreover from `c = \<lparr>\<delta>\<rparr> r` and `r = \<nu> b. R b` and `\<And>b. R b = P x b` have "c = \<lparr>\<delta>\<rparr> \<nu> b. P x b"
        by simp
      ultimately have "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>c"
        by (blast intro: proper_transition.simple)
      then show ?thesis
        using proper.bisimilarity_reflexivity and proper.lift_reflexivity_propagation and reflpD
        by smt
    qed
  next
    case (output_without_opening a' x r)
    from `\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>a' \<triangleleft> x\<rbrace> r` show ?thesis
    proof cases
      case (scoped_acting Q R)
      from `\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b` have "\<And>b. Q b = a \<triangleright> x. P x b"
        by (fact opening_transitions_from_new_channel_receive)
      with `\<And>b. Q b \<rightarrow>\<^sub>\<flat>\<lbrace>a' \<triangleleft> x\<rbrace> R b` show ?thesis
        using basic_transitions_from_receive and basic_residual.inject(1)
        by fastforce
    qed
  next
    case (output_with_opening Q a' K)
    from `\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b` have "\<And>b. Q b = a \<triangleright> x. P x b"
      by (fact opening_transitions_from_new_channel_receive)
    with `\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a' \<triangleleft> K b` have "a \<triangleright> x. P x undefined \<rightarrow>\<^sub>\<sharp>\<lparr>a' \<triangleleft> K undefined"
      by simp
    then show ?thesis
    proof cases
      case (output_without_opening x q)
      then show ?thesis
        using basic_transitions_from_receive
        by fastforce
    next
      case output_with_opening
      then show ?thesis by (simp add: no_opening_transitions_from_receive)
    qed
  qed
qed

lemma proper_receive_scope_extension: "a \<triangleright> x. \<nu> b. P x b \<sim>\<^sub>\<sharp> \<nu> b. a \<triangleright> x. P x b"
  by standard (
    fact proper_pre_receive_scope_extension_ltr,
    fact proper_pre_receive_scope_extension_rtl
  )

end

lemma proper_parallel_scope_extension: "\<nu> a. P a \<parallel> q \<sim>\<^sub>\<sharp> \<nu> a. (P a \<parallel> q)"
  using basic_parallel_scope_extension
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<sim>\<^sub>\<sharp> \<nu> a. \<nu> b. P a b"
  using basic_new_channel_scope_extension
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_parallel_unit: "\<zero> \<parallel> p \<sim>\<^sub>\<sharp> p"
  using basic_parallel_unit
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_parallel_commutativity: "p \<parallel> q \<sim>\<^sub>\<sharp> q \<parallel> p"
  using basic_parallel_commutativity
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_parallel_associativity: "(p \<parallel> q) \<parallel> r \<sim>\<^sub>\<sharp> p \<parallel> (q \<parallel> r)"
  using basic_parallel_associativity
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

context begin

private lemma opening_transitions_from_new_channel_stop: "\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<Longrightarrow> P a = \<zero>"
proof -
  fix P and a
  assume "\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a"
  then show "P a = \<zero>"
  proof (induction "\<nu> a. \<zero>" "\<lbrace>\<nu> a\<rbrace> P a" arbitrary: P)
    case opening
    show ?case by (fact refl)
  next
    case scoped_opening
    then show ?case using no_basic_transitions_from_stop by metis
  qed
qed

private lemma no_acting_transitions_from_new_channel_stop: "\<not> \<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p"
proof
  fix \<alpha> and p
  assume "\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p"
  then show False
  proof cases
    case (scoped_acting Q\<^sub>1 Q\<^sub>2)
    from `\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q\<^sub>1 a` have "\<And>a. Q\<^sub>1 a = \<zero>"
      by (fact opening_transitions_from_new_channel_stop)
    with `\<And>a. Q\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q\<^sub>2 a` show ?thesis
      by (simp add: no_basic_transitions_from_stop)
  qed
qed

private lemma no_proper_transitions_from_new_channel_stop: "\<not> \<nu> a. \<zero> \<rightarrow>\<^sub>\<sharp>c"
proof
  fix c
  assume "\<nu> a. \<zero> \<rightarrow>\<^sub>\<sharp>c"
  then show False
  proof cases
    case (output_with_opening P a K)
    from `\<nu> b. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P b` have "\<And>b. P b = \<zero>"
      by (fact opening_transitions_from_new_channel_stop)
    with `\<And>b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> K b` show ?thesis
      by (simp add: no_proper_transitions_from_stop)
  qed (simp_all add: no_acting_transitions_from_new_channel_stop)
qed

private lemma proper_stop_scope_redundancy: "\<zero> \<sim>\<^sub>\<sharp> \<nu> a. \<zero>"
proof
  show "\<zero> \<lesssim>\<^sub>\<sharp> \<nu> a. \<zero>"
    using no_proper_transitions_from_stop
    by (blast intro: proper.pre_bisimilarity.intros)
next
  show "\<nu> a. \<zero> \<lesssim>\<^sub>\<sharp> \<zero>"
    using no_proper_transitions_from_new_channel_stop
    by (blast intro: proper.pre_bisimilarity.intros)
qed

lemma proper_scope_redundancy: "p \<sim>\<^sub>\<sharp> \<nu> a. p"
proof -
  have "p \<sim>\<^sub>\<sharp> \<zero> \<parallel> p"
    by (rule proper.bisimilarity_symmetry_rule) (fact proper_parallel_unit)
  also have "\<zero> \<parallel> p \<sim>\<^sub>\<sharp> \<nu> a. \<zero> \<parallel> p"
    using proper_stop_scope_redundancy and proper_parallel_preservation by blast
  also have "\<nu> a. \<zero> \<parallel> p \<sim>\<^sub>\<sharp> \<nu> a. (\<zero> \<parallel> p)"
    by (fact proper_parallel_scope_extension)
  also have "\<nu> a. (\<zero> \<parallel> p) \<sim>\<^sub>\<sharp> \<nu> a. p"
    using proper_parallel_unit and proper_new_channel_preservation by metis
  finally show ?thesis .
qed

end

subsection \<open>Conclusion\<close>

text \<open>
  This is all for the proper transition system.
\<close>

end
