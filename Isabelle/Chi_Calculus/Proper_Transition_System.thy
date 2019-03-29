section \<open>Proper Transition System\<close>

theory Proper_Transition_System
  imports Basic_Transition_System
begin

subsection \<open>Actions\<close>

text \<open>
  Actions include input actions and the internal action.
\<close>

datatype proper_action =
  ProperIn \<open>chan\<close> \<open>val\<close> (infix "\<triangleright>" 100) |
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

datatype 't output_rest =
  WithoutOpening \<open>val\<close> \<open>'t\<close> ("_\<rparr> _" [52, 51] 51) |
  WithOpening \<open>chan \<Rightarrow> 't output_rest\<close> (binder "\<nu>" 51)

text \<open>
  Note that the definition of \<open>output_rest\<close> is actually more permissive than the verbal definition
  of output rests above: the number of scope openings of a particular \<open>output_rest\<close> value is not
  necessarily fixed, since the structure of a follow-up output rest in a \<open>WithOpening\<close> value can
  depend on the given channel. This is just to keep the definition simple. It does not cause any
  problems in our later proofs.
\<close>

text \<open>
  Interestingly, equipping \<^type>\<open>output_rest\<close> with \<^const>\<open>rel_output_rest\<close> leads to a residual
  structure, despite the fact that output rests are not intended to serve as residuals but only as
  components of residuals.
\<close>

interpretation output_rest: residual rel_output_rest
  by
    unfold_locales
    (
      fact output_rest.rel_mono,
      fact output_rest.rel_eq,
      fact output_rest.rel_compp,
      fact output_rest.rel_conversep
    )

subsection \<open>Residuals\<close>

text \<open>
  There are two kinds of residuals in the proper transition system: simple residuals, written
  \<open>\<lparr>\<delta>\<rparr> q\<close> where \<open>\<delta>\<close> is an action, and output residuals, written
  \<open>\<lparr>a \<triangleleft> \<nu> b\<^sub>1 \<dots> b\<^sub>n. X b\<^sub>1 \<dots> b\<^sub>n\<rparr> Q b\<^sub>1 \<dots> b\<^sub>n\<close> where \<open>a\<close> is a channel and the \<open>b\<^sub>i\<close> are channel variables.
\<close>

datatype 't proper_residual =
  Simple \<open>proper_action\<close> \<open>'t\<close> ("\<lparr>_\<rparr> _" [0, 51] 51) |
  Output \<open>chan\<close> \<open>'t output_rest\<close> ("\<lparr>_ \<triangleleft> _" [0, 51] 51)

text \<open>
  Equipping \<^type>\<open>proper_residual\<close> with \<^const>\<open>rel_proper_residual\<close> leads to a residual structure.
\<close>

interpretation proper: residual rel_proper_residual
  by
    unfold_locales
    (
      fact proper_residual.rel_mono,
      fact proper_residual.rel_eq,
      fact proper_residual.rel_compp,
      fact proper_residual.rel_conversep
    )

subsection \<open>Transition System\<close>

text \<open>
  The following definition of the transition relation captures the set of rules that define the
  transition system.
\<close>

inductive
  proper_transition :: "process \<Rightarrow> process proper_residual \<Rightarrow> bool"
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

interpretation proper: transition_system rel_proper_residual proper_transition
  by intro_locales

text \<open>
  We introduce concise notation for some of the derived predicates of the transition system.
\<close>

notation proper.pre_bisimilarity (infix "\<lesssim>\<^sub>\<sharp>" 50)
notation proper.bisimilarity (infix "\<sim>\<^sub>\<sharp>" 50)

subsection \<open>Fundamental Properties of the Transition System\<close>

lemma no_proper_transitions_from_stop: "\<not> \<zero> \<rightarrow>\<^sub>\<sharp>c"
proof
  fix c
  assume "\<zero> \<rightarrow>\<^sub>\<sharp>c"
  then show False
    by cases (simp_all add: no_basic_transitions_from_stop)
qed

subsection \<open>Relationships between Basic and Proper Bisimilarity\<close>

lemma basic_bisimilarity_is_proper_simulation: "proper.sim (\<sim>\<^sub>\<flat>)"
proof (intro predicate2I, intro allI, intro impI)
  fix p and q and c
  assume "p \<rightarrow>\<^sub>\<sharp>c" and "p \<sim>\<^sub>\<flat> q"
  then show "\<exists>d. q \<rightarrow>\<^sub>\<sharp>d \<and> rel_proper_residual (\<sim>\<^sub>\<flat>) c d"
  proof (induction arbitrary: q)
    case (simple p \<delta> p' q)
    from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> p'\<close>
    obtain q' where "q \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
      using
        basic.bisimilarity_is_simulation and
        predicate2D and
        basic_residual.rel_cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then show ?case
      by (blast intro: proper_transition.simple proper_residual.rel_intros(1))
  next
    case (output_without_opening p a x p' q)
    from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> p'\<close>
    obtain q' where "q \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
      using
        basic.bisimilarity_is_simulation and
        predicate2D and
        basic_residual.rel_cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then show ?case
      by (blast intro: proper_transition.output_without_opening output_rest.rel_intros(1) proper_residual.rel_intros(2))
  next
    case (output_with_opening p P a K q)
    obtain Q where "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<And>a. P a \<sim>\<^sub>\<flat> Q a"
    proof -
      from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close>
      obtain d where "q \<rightarrow>\<^sub>\<flat>d" and "rel_basic_residual (\<sim>\<^sub>\<flat>) (\<lbrace>\<nu> a\<rbrace> P a) d"
        using basic.bisimilarity_is_simulation
        by blast
      from \<open>rel_basic_residual (\<sim>\<^sub>\<flat>) (\<lbrace>\<nu> a\<rbrace> P a) d\<close> and \<open>q \<rightarrow>\<^sub>\<flat>d\<close> and that show ?thesis
        by cases (auto elim: rel_funE)
    qed
    (*
      In case we provide lemmas or proof methods for statements that we currently solve with smt,
      note that the above statement was formerly also proved using smt (after the dropping of
      contexts this surprisingly did not work anymore). Here is the old code:

          from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close>
          obtain Q where "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<And>a. P a \<sim>\<^sub>\<flat> Q a"
            using
              basic.bisimilarity_is_simulation and
              predicate2D and
              basic_lift.cases and
              basic_residual.distinct(1) and
              basic_residual.inject(2)
            by smt
    *)
    obtain L where "\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b" and "\<And>b. rel_output_rest (\<sim>\<^sub>\<flat>) (K b) (L b)"
    proof -
      from output_with_opening.IH and \<open>\<And>b. P b \<sim>\<^sub>\<flat> Q b\<close>
      have "\<forall>b. \<exists>l. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> l \<and> rel_output_rest (\<sim>\<^sub>\<flat>) (K b) l"
        using
          proper_residual.rel_cases and
          proper_residual.distinct(1) and
          proper_residual.inject(2)
        by smt
      then have "\<exists>L. \<forall>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b \<and> rel_output_rest (\<sim>\<^sub>\<flat>) (K b) (L b)"
        by (fact choice)
      with that show ?thesis by blast
    qed
    from \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b\<close> and \<open>\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b\<close> have "q \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. L b"
      by (fact proper_transition.output_with_opening)
    with \<open>\<And>a. rel_output_rest (\<sim>\<^sub>\<flat>) (K a) (L a)\<close> show ?case
      using output_rest.rel_intros(2) and rel_funI and proper_residual.rel_intros(2)
      by smt
  qed
qed

lemma basic_bisimilarity_is_proper_bisimulation: "proper.bisim (\<sim>\<^sub>\<flat>)"
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

lemma proper_parallel_preservation_left: "p\<^sub>1 \<sim>\<^sub>\<sharp> p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<parallel> q \<sim>\<^sub>\<sharp> p\<^sub>2 \<parallel> q"
  sorry

lemma proper_parallel_preservation_right: "q\<^sub>1 \<sim>\<^sub>\<sharp> q\<^sub>2 \<Longrightarrow> p \<parallel> q\<^sub>1 \<sim>\<^sub>\<sharp> p \<parallel> q\<^sub>2"
  sorry

lemma proper_parallel_preservation: "\<lbrakk>p\<^sub>1 \<sim>\<^sub>\<sharp> p\<^sub>2; q\<^sub>1 \<sim>\<^sub>\<sharp> q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<sim>\<^sub>\<sharp> p\<^sub>2 \<parallel> q\<^sub>2"
  sorry

lemma proper_new_channel_preservation: "(\<And>a. P a \<sim>\<^sub>\<sharp> Q a) \<Longrightarrow> \<nu> a. P a \<sim>\<^sub>\<sharp> \<nu> a. Q a"
  sorry

context begin

private lemma proper_pre_receive_scope_extension_ltr: "a \<triangleright> x. \<nu> b. P x b \<lesssim>\<^sub>\<sharp> \<nu> b. a \<triangleright> x. P x b"
proof (standard, intro allI, intro impI)
  fix c
  assume "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>c"
  then show "\<exists>d. \<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>d \<and> rel_proper_residual (\<sim>\<^sub>\<sharp>) c d"
  proof cases
    case (simple \<delta> q)
    from \<open>a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q\<close>
    obtain x where "basic_action_of \<delta> = a \<triangleright> x" and "q = \<nu> b. P x b"
      by (blast elim: basic_transitions_from_receive)
    from \<open>basic_action_of \<delta> = a \<triangleright> x\<close> have "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> b. P x b"
      using receiving and acting_scope
      by smt
    with \<open>c = \<lparr>\<delta>\<rparr> q\<close> and \<open>q = \<nu> b. P x b\<close> have "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>c"
      by (blast intro: proper_transition.simple)
    then show ?thesis
      using proper.bisimilarity_reflexivity and proper.lift_reflexivity_propagation and reflpD
      by smt
  next
    case (output_without_opening a x q)
    then show ?thesis
      by (blast elim: basic_transitions_from_receive)
  next
    case output_with_opening
    then show ?thesis
      using no_opening_transitions_from_receive
      by simp
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
  then show "\<exists>d. a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>d \<and> rel_proper_residual (\<sim>\<^sub>\<sharp>) c d"
  proof cases
    case (simple \<delta> r)
    from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> r\<close> show ?thesis
    proof cases
      case (scoped_acting Q R)
      from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b\<close> have "\<And>b. Q b = a \<triangleright> x . P x b"
        by (fact opening_transitions_from_new_channel_receive)
      with \<open>\<And>b. Q b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> R b\<close>
      obtain x where "basic_action_of \<delta> = a \<triangleright> x" and "\<And>b. R b = P x b"
        using
          basic_transitions_from_receive and
          basic_residual.inject(1) and
          basic_action.inject(1) and
          io_action.inject(2)
        by smt
      from \<open>basic_action_of \<delta> = a \<triangleright> x\<close> have "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> b. P x b"
        by (auto intro: receiving)
      moreover from \<open>c = \<lparr>\<delta>\<rparr> r\<close> and \<open>r = \<nu> b. R b\<close> and \<open>\<And>b. R b = P x b\<close> have "c = \<lparr>\<delta>\<rparr> \<nu> b. P x b"
        by simp
      ultimately have "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>c"
        by (blast intro: proper_transition.simple)
      then show ?thesis
        using proper.bisimilarity_reflexivity and proper.lift_reflexivity_propagation and reflpD
        by smt
    qed
  next
    case (output_without_opening a' x r)
    from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>a' \<triangleleft> x\<rbrace> r\<close> show ?thesis
    proof cases
      case (scoped_acting Q R)
      from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b\<close> have "\<And>b. Q b = a \<triangleright> x. P x b"
        by (fact opening_transitions_from_new_channel_receive)
      with \<open>\<And>b. Q b \<rightarrow>\<^sub>\<flat>\<lbrace>a' \<triangleleft> x\<rbrace> R b\<close> show ?thesis
        by (auto elim: basic_transitions_from_receive)
    qed
  next
    case (output_with_opening Q a' K)
    from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b\<close> have "\<And>b. Q b = a \<triangleright> x. P x b"
      by (fact opening_transitions_from_new_channel_receive)
    with \<open>\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a' \<triangleleft> K b\<close> have "a \<triangleright> x. P x undefined \<rightarrow>\<^sub>\<sharp>\<lparr>a' \<triangleleft> K undefined"
      by simp
    then show ?thesis
    proof cases
      case (output_without_opening x q)
      then show ?thesis
        by (blast elim: basic_transitions_from_receive)
    next
      case output_with_opening
      then show ?thesis
        using no_opening_transitions_from_receive
        by simp
    qed
  qed
qed

lemma proper_receive_scope_extension: "a \<triangleright> x. \<nu> b. P x b \<sim>\<^sub>\<sharp> \<nu> b. a \<triangleright> x. P x b"
  by standard (
    fact proper_pre_receive_scope_extension_ltr,
    fact proper_pre_receive_scope_extension_rtl
  )

end

lemma proper_parallel_scope_extension_left: "\<nu> a. P a \<parallel> q \<sim>\<^sub>\<sharp> \<nu> a. (P a \<parallel> q)"
  using basic_parallel_scope_extension_left
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_parallel_scope_extension_right: "p \<parallel> \<nu> a. Q a \<sim>\<^sub>\<sharp> \<nu> a. (p \<parallel> Q a)"
  sorry

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
    from \<open>\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q\<^sub>1 a\<close> have "\<And>a. Q\<^sub>1 a = \<zero>"
      by (fact opening_transitions_from_new_channel_stop)
    with \<open>\<And>a. Q\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q\<^sub>2 a\<close> show ?thesis
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
    from \<open>\<nu> b. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P b\<close> have "\<And>b. P b = \<zero>"
      by (fact opening_transitions_from_new_channel_stop)
    with \<open>\<And>b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> K b\<close> show ?thesis
      by (simp add: no_proper_transitions_from_stop)
  qed (simp_all add: no_acting_transitions_from_new_channel_stop)
qed

private lemma proper_stop_scope_redundancy: "\<zero> \<sim>\<^sub>\<sharp> \<nu> a. \<zero>"
proof
  show "\<zero> \<lesssim>\<^sub>\<sharp> \<nu> a. \<zero>"
    using no_proper_transitions_from_stop
    by (blast intro: proper.pre_bisimilarity)
next
  show "\<nu> a. \<zero> \<lesssim>\<^sub>\<sharp> \<zero>"
    using no_proper_transitions_from_new_channel_stop
    by (blast intro: proper.pre_bisimilarity)
qed

lemma proper_scope_redundancy: "p \<sim>\<^sub>\<sharp> \<nu> a. p"
proof -
  have "p \<sim>\<^sub>\<sharp> \<zero> \<parallel> p"
    by (rule proper.bisimilarity_symmetry_rule) (fact proper_parallel_unit)
  also have "\<zero> \<parallel> p \<sim>\<^sub>\<sharp> \<nu> a. \<zero> \<parallel> p"
    using proper_stop_scope_redundancy and proper_parallel_preservation_left by blast
  also have "\<nu> a. \<zero> \<parallel> p \<sim>\<^sub>\<sharp> \<nu> a. (\<zero> \<parallel> p)"
    by (fact proper_parallel_scope_extension_left)
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
