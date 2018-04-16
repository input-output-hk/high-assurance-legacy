theory Bisimulation
  imports Transition_System "HOL-Eisbach.Eisbach"
begin

inductive
  basic_residual_lifting :: "
    (('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool) \<Rightarrow>
    ('name, 'chan, 'val) basic_residual \<Rightarrow>
    ('name, 'chan, 'val) basic_residual \<Rightarrow>
    bool"
where
  acting_lifting:
    "\<X> P Q \<Longrightarrow> basic_residual_lifting \<X> (\<lbrace>\<alpha>\<rbrace> P) (\<lbrace>\<alpha>\<rbrace> Q)" |
  opening_lifting:
    "(\<And>a. \<X> (\<P> a) (\<Q> a)) \<Longrightarrow> basic_residual_lifting \<X> (\<lbrace>\<nu> a\<rbrace> \<P> a) (\<lbrace>\<nu> a\<rbrace> \<Q> a)"

lemma basic_residual_lifting_reflexivity:
  assumes reflexivity: "\<And>P. \<X> P P"
  shows "basic_residual_lifting \<X> C C"
proof (cases C)
  case Acting
  then show ?thesis by (simp add: reflexivity acting_lifting)
next
  case Opening
  then show ?thesis by (simp add: reflexivity opening_lifting)
qed

lemma basic_residual_lifting_symmetry:
  assumes symmetry: "\<And>P Q. \<X> P Q \<Longrightarrow> \<X> Q P"
  assumes hypothesis: "basic_residual_lifting \<X> C D"
  shows "basic_residual_lifting \<X> D C"
using hypothesis proof cases
  case acting_lifting
  then show ?thesis by (simp add: symmetry basic_residual_lifting.acting_lifting)
next
  case opening_lifting
  then show ?thesis by (simp add: symmetry basic_residual_lifting.opening_lifting)
qed

lemma basic_residual_lifting_transitivity:
  assumes transitivity: "\<And>P Q R. \<lbrakk> \<X> P Q; \<X> Q R \<rbrakk> \<Longrightarrow> \<X> P R"
  assumes hypotheses: "basic_residual_lifting \<X> C D" "basic_residual_lifting \<X> D E"
  shows "basic_residual_lifting \<X> C E"
proof (cases D)
  case Acting
  then show ?thesis
    using
      hypotheses and
      basic_residual_lifting.cases and
      basic_residual.inject(1) and
      basic_residual.distinct(2) and
      transitivity and
      acting_lifting
    by (metis (no_types, lifting))
next
  case Opening
  then show ?thesis
    using
      hypotheses and
      basic_residual_lifting.cases and
      basic_residual.distinct(1) and
      basic_residual.inject(2) and
      transitivity and
      opening_lifting
    by smt
qed

lemma basic_residual_lifting_monotonicity:
  "\<X> \<le> \<Y> \<Longrightarrow> basic_residual_lifting \<X> \<le> basic_residual_lifting \<Y>"
  using basic_residual_lifting.simps and predicate2D and predicate2I
  by smt

abbreviation
  basic_transition_transfer :: "
    (('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where "
  basic_transition_transfer \<X> P Q \<equiv>
    \<forall>\<Gamma> C. \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>C \<longrightarrow> (\<exists>D. \<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting \<X> C D)"

lemma basic_transition_transfer_monotonicity:
  "\<X> \<le> \<Y> \<Longrightarrow> basic_transition_transfer \<X> \<le> basic_transition_transfer \<Y>"
  using basic_residual_lifting_monotonicity
  by blast

abbreviation
  is_basic_simulation :: "
    (('name, 'chan, 'val) process \<Rightarrow>('name, 'chan, 'val) process \<Rightarrow> bool) \<Rightarrow> bool"
  ("sim\<^sub>\<flat> _")
where
  "sim\<^sub>\<flat> \<X> \<equiv> \<forall>P Q. \<X> P Q \<longrightarrow> basic_transition_transfer \<X> P Q"

abbreviation
  is_basic_bisimulation:: "
    (('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool) \<Rightarrow> bool"
  ("bisim\<^sub>\<flat> _")
where
  "bisim\<^sub>\<flat> \<X> \<equiv> sim\<^sub>\<flat> \<X> \<and> sim\<^sub>\<flat> (\<lambda>P Q. \<X> Q P)"

lemma symmetric_basic_simulation:
  assumes symmetry: "\<And>P Q. \<X> P Q \<Longrightarrow> \<X> Q P"
  assumes is_simulation: "sim\<^sub>\<flat> \<X>"
  shows "bisim\<^sub>\<flat> \<X>"
proof
  show "sim\<^sub>\<flat> \<X>" by (intro is_simulation)
next
  show "sim\<^sub>\<flat> \<lambda>P Q. \<X> Q P"
    using symmetry and is_simulation and basic_residual_lifting.simps
    by smt
qed

coinductive
  basic_pre_bisimilarity :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
  (infix "\<preceq>\<^sub>\<flat>" 50)
and
  basic_bisimilarity :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
  (infix "\<sim>\<^sub>\<flat>" 50)
where
  "basic_transition_transfer op \<sim>\<^sub>\<flat> P Q \<Longrightarrow> P \<preceq>\<^sub>\<flat> Q" |
  "P \<sim>\<^sub>\<flat> Q \<equiv> P \<preceq>\<^sub>\<flat> Q \<and> Q \<preceq>\<^sub>\<flat> P"
monos basic_residual_lifting_monotonicity

lemma basic_pre_bisimilarity_reflexivity: "P \<preceq>\<^sub>\<flat> P"
proof (coinduction arbitrary: P)
  case basic_pre_bisimilarity
  then show ?case
    using basic_residual_lifting_reflexivity
    by (metis (mono_tags, lifting))
qed

lemma basic_bisimilarity_reflexivity: "P \<sim>\<^sub>\<flat> P"
  using basic_pre_bisimilarity_reflexivity by simp

lemma basic_bisimilarity_symmetry [sym]: "P \<sim>\<^sub>\<flat> Q \<Longrightarrow> Q \<sim>\<^sub>\<flat> P"
  by simp

lemma basic_bisimilarity_is_basic_simulation: "sim\<^sub>\<flat> op \<sim>\<^sub>\<flat>"
  using basic_pre_bisimilarity.cases
  by (metis (mono_tags, lifting))

lemma basic_bisimilarity_is_basic_bisimulation: "bisim\<^sub>\<flat> op \<sim>\<^sub>\<flat>"
  using basic_bisimilarity_symmetry and basic_bisimilarity_is_basic_simulation
  by (intro symmetric_basic_simulation)

lemma basic_pre_bisimilarity_contains_all_basic_bisimulations: "bisim\<^sub>\<flat> \<X> \<Longrightarrow> \<X> \<le> op \<preceq>\<^sub>\<flat>"
proof
  assume "bisim\<^sub>\<flat> \<X>"
  fix P and Q
  assume "\<X> P Q"
  then have "\<X> P Q \<or> \<X> Q P" by (intro disjI1)
  then show "P \<preceq>\<^sub>\<flat> Q"
  proof (coinduction arbitrary: P Q)
    case basic_pre_bisimilarity
    then have transfer: "basic_transition_transfer (\<lambda>P Q. \<X> P Q \<or> \<X> Q P) P Q"
    proof
      assume "\<X> P Q"
      with `bisim\<^sub>\<flat> \<X>` show ?thesis
        using basic_residual_lifting_monotonicity and predicate2I and predicate2D
        by (metis (no_types, lifting))
    next
      assume "\<X> Q P"
      with `bisim\<^sub>\<flat> \<X>` show ?thesis
        using basic_residual_lifting_monotonicity and predicate2I and predicate2D
        by (metis (no_types, lifting))
    qed
    let
      ?target_relation = "\<lambda>P Q.
        ((\<exists>S T. P = S \<and> Q = T \<and> (\<X> S T \<or> \<X> T S)) \<or> P \<preceq>\<^sub>\<flat> Q) \<and>
        ((\<exists>S T. Q = S \<and> P = T \<and> (\<X> S T \<or> \<X> T S)) \<or> Q \<preceq>\<^sub>\<flat> P)"
    have inclusion: "(\<lambda>P Q. \<X> P Q \<or> \<X> Q P) \<le> ?target_relation"
      by blast
    from inclusion and transfer have "basic_transition_transfer ?target_relation P Q"
      using basic_transition_transfer_monotonicity
      by blast
    then show ?case by blast
  qed
qed

lemma basic_bisimilarity_contains_all_basic_bisimulations: "bisim\<^sub>\<flat> \<X> \<Longrightarrow> \<X> \<le> op \<sim>\<^sub>\<flat>"
proof
  assume "bisim\<^sub>\<flat> \<X>"
  fix P and Q
  assume "\<X> P Q"
  show "P \<sim>\<^sub>\<flat> Q"
  proof
    from `bisim\<^sub>\<flat> \<X>` and `\<X> P Q` show "P \<preceq>\<^sub>\<flat> Q"
      using basic_pre_bisimilarity_contains_all_basic_bisimulations
      by blast
  next
    from `bisim\<^sub>\<flat> \<X>` have "bisim\<^sub>\<flat> \<lambda>P Q. \<X> Q P"
      by simp
    then have "(\<lambda>P Q. \<X> Q P) \<le> op \<preceq>\<^sub>\<flat>"
      by (intro basic_pre_bisimilarity_contains_all_basic_bisimulations)
    with `\<X> P Q` show "Q \<preceq>\<^sub>\<flat> P"
      by blast
  qed
qed

lemma basic_bisimilarity_transitivity [trans]: "\<lbrakk> P \<sim>\<^sub>\<flat> Q; Q \<sim>\<^sub>\<flat> R \<rbrakk> \<Longrightarrow> P \<sim>\<^sub>\<flat> R"
proof -
  let ?have_intermediate = "\<lambda>P R. \<exists>Q. P \<sim>\<^sub>\<flat> Q \<and> Q \<sim>\<^sub>\<flat> R"
  have "\<And>P R. ?have_intermediate P R \<Longrightarrow> ?have_intermediate R P"
    by blast
  moreover
  have "sim\<^sub>\<flat> ?have_intermediate"
  proof ((intro allI)+, intro impI)
    fix P and R
    assume "?have_intermediate P R"
    then obtain Q where "P \<sim>\<^sub>\<flat> Q" and "Q \<sim>\<^sub>\<flat> R"
      by blast
    show "basic_transition_transfer ?have_intermediate P R"
    proof (intro allI impI)+
      fix \<Gamma> and C
      assume "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>C"
      from `P \<sim>\<^sub>\<flat> Q` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>C`
      obtain D where "\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>D" and "basic_residual_lifting op \<sim>\<^sub>\<flat> C D"
        using basic_bisimilarity_is_basic_simulation
        by blast
      from `Q \<sim>\<^sub>\<flat> R` and `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>D`
      obtain E where "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>E" and "basic_residual_lifting op \<sim>\<^sub>\<flat> D E"
        using basic_bisimilarity_is_basic_simulation
        by blast
      have "basic_residual_lifting ?have_intermediate C E"
      proof (cases D)
        case Acting
        with `basic_residual_lifting op \<sim>\<^sub>\<flat> C D` and `basic_residual_lifting op \<sim>\<^sub>\<flat> D E`
        show ?thesis
          using
            basic_residual_lifting.simps and
            basic_residual.inject(1) and
            basic_residual.distinct(2) and
            acting_lifting
          by smt
      next
        case Opening
        with `basic_residual_lifting op \<sim>\<^sub>\<flat> C D` and `basic_residual_lifting op \<sim>\<^sub>\<flat> D E`
        show ?thesis
          using
            basic_residual_lifting.simps and
            basic_residual.distinct(1) and
            basic_residual.inject(2) and
            opening_lifting
          by smt
      qed
      with `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>E` show "\<exists>E. \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>E \<and> basic_residual_lifting ?have_intermediate C E"
        by blast
    qed
  qed
  ultimately have "bisim\<^sub>\<flat> ?have_intermediate"
    by (intro symmetric_basic_simulation)
  then have "?have_intermediate \<le> op \<sim>\<^sub>\<flat>"
    by (intro basic_bisimilarity_contains_all_basic_bisimulations)
  then show "\<lbrakk> P \<sim>\<^sub>\<flat> Q; Q \<sim>\<^sub>\<flat> R \<rbrakk> \<Longrightarrow> P \<sim>\<^sub>\<flat> R"
    by blast
qed

lemma is_simulation_scoped_acting_worker:
  fixes S and \<S>\<^sub>1
  fixes \<X> :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
  assumes with_new_channel:
    "\<And>\<P> \<Q>. (\<And>a. \<X> (\<P> a) (\<Q> a)) \<Longrightarrow> \<X> (\<nu> a. \<P> a) (\<nu> a. \<Q> a)"
  assumes step_1:
    "\<And>T. \<X> S T \<Longrightarrow> \<exists>D\<^sub>1. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D\<^sub>1 \<and> basic_residual_lifting \<X> (\<lbrace>\<nu> a\<rbrace> \<S>\<^sub>1 a) D\<^sub>1"
  assumes step_2:
    "\<And>a T\<^sub>1. \<X> (\<S>\<^sub>1 a) T\<^sub>1 \<Longrightarrow> \<exists>D\<^sub>2. \<Gamma> \<turnstile> T\<^sub>1 \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_residual_lifting \<X> (\<lbrace>\<alpha>\<rbrace> \<S>\<^sub>2 a) D\<^sub>2"
  assumes initial_relation:
    "\<X> S T"
  shows
    "\<exists>D\<^sub>2. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_residual_lifting \<X> (\<lbrace>\<alpha>\<rbrace> \<nu> a. \<S>\<^sub>2 a) D\<^sub>2"
proof -
  from step_1 and `\<X> S T`
  obtain \<T>\<^sub>1 where "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and "\<And>a. \<X> (\<S>\<^sub>1 a) (\<T>\<^sub>1 a)"
    using
      basic_residual_lifting.cases and
      basic_residual.distinct(1) and
      basic_residual.inject(2)
    by (metis (full_types))
  obtain \<T>\<^sub>2 where "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a" and "\<And>a. \<X> (\<S>\<^sub>2 a) (\<T>\<^sub>2 a)"
  proof -
    from step_2 and `\<And>a. \<X> (\<S>\<^sub>1 a) (\<T>\<^sub>1 a)`
    have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> \<X> (\<S>\<^sub>2 a) H"
      using
        basic_residual_lifting.cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then have "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a \<and> \<X> (\<S>\<^sub>2 a) (\<T>\<^sub>2 a)"
      by (intro choice)
    with that show ?thesis by blast
  qed
  from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
    by (intro basic_transition.scoped_acting)
  with `\<And>a. \<X> (\<S>\<^sub>2 a) (\<T>\<^sub>2 a)` show ?thesis
    using with_new_channel and acting_lifting
    by blast
qed

method is_simulation_scoped_acting
  for S :: "('name, 'chan, 'val) process" and \<S>\<^sub>1 :: "'chan \<Rightarrow> ('name, 'chan, 'val) process"
  uses with_new_channel
= (
  intro is_simulation_scoped_acting_worker [where S = S and \<S>\<^sub>1 = \<S>\<^sub>1],
  intro with_new_channel,
  blast+
)

lemma is_simulation_scoped_opening_worker:
  fixes \<X> :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
  assumes with_new_channel:
    "\<And>\<P> \<Q>. (\<And>a. \<X> (\<P> a) (\<Q> a)) \<Longrightarrow> \<X> (\<nu> a. \<P> a) (\<nu> a. \<Q> a)"
  assumes step_1:
    "\<And>T. \<X> S T \<Longrightarrow> \<exists>D\<^sub>1. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D\<^sub>1 \<and> basic_residual_lifting \<X> (\<lbrace>\<nu> a\<rbrace> \<S>\<^sub>1 a) D\<^sub>1"
  assumes step_2:
    "\<And>a T\<^sub>1. \<X> (\<S>\<^sub>1 a) T\<^sub>1 \<Longrightarrow> \<exists>D\<^sub>2. \<Gamma> \<turnstile> T\<^sub>1 \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_residual_lifting \<X> (\<lbrace>\<nu> b\<rbrace> \<S>\<^sub>2 a b) D\<^sub>2"
  assumes initial_relation:
    "\<X> S T"
  shows
    "\<exists>D\<^sub>2. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D\<^sub>2 \<and> basic_residual_lifting \<X> (\<lbrace>\<nu> b\<rbrace> \<nu> a. \<S>\<^sub>2 a b) D\<^sub>2"
proof -
  from step_1 and `\<X> S T`
  obtain \<T>\<^sub>1 where "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and "\<And>a. \<X> (\<S>\<^sub>1 a) (\<T>\<^sub>1 a)"
    using
      basic_residual_lifting.cases and
      basic_residual.distinct(1) and
      basic_residual.inject(2)
    by (metis (full_types))
  obtain \<T>\<^sub>2 where "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b" and "\<And>a b. \<X> (\<S>\<^sub>2 a b) (\<T>\<^sub>2 a b)"
  proof -
    from step_2 and `\<And>a. \<X> (\<S>\<^sub>1 a) (\<T>\<^sub>1 a)`
    have "\<forall>a. \<exists>\<H>. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. \<X> (\<S>\<^sub>2 a b) (\<H> b))"
      using
        basic_residual_lifting.cases and
        basic_residual.distinct(1) and
        basic_residual.inject(2)
      by smt
    then have "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b \<and> (\<forall>b. \<X> (\<S>\<^sub>2 a b) (\<T>\<^sub>2 a b))"
      by (intro choice)
    with that show ?thesis by blast
  qed
  from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<T>\<^sub>2 a b"
    by (intro basic_transition.scoped_opening)
  with `\<And>a b. \<X> (\<S>\<^sub>2 a b) (\<T>\<^sub>2 a b)` show ?thesis
    using with_new_channel and opening_lifting
    by smt
qed

method is_simulation_scoped_opening
  for S :: "('name, 'chan, 'val) process" and \<S>\<^sub>1 :: "'chan \<Rightarrow> ('name, 'chan, 'val) process"
  uses with_new_channel
= (
  intro is_simulation_scoped_opening_worker [where S = S and \<S>\<^sub>1 = \<S>\<^sub>1],
  intro with_new_channel,
  blast+
)

lemma pre_unicast_input_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x) \<Longrightarrow> c \<triangleright> x. \<P> x \<preceq>\<^sub>\<flat> c \<triangleright> x. \<Q> x"
proof (standard, (intro allI impI)+)
  assume "\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x"
  fix \<Gamma> and C
  assume "\<Gamma> \<turnstile> c \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>C"
  then show "\<exists>D. \<Gamma> \<turnstile> c \<triangleright> x. \<Q> x \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting op \<sim>\<^sub>\<flat> C D"
  proof cases
    case unicast_input
    with `\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x` show ?thesis
      using basic_transition.unicast_input and acting_lifting
      by (metis (no_types, lifting))
  qed (simp_all add: no_opening_transitions_from_unicast_input)
qed

lemma unicast_input_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x) \<Longrightarrow> c \<triangleright> x. \<P> x \<sim>\<^sub>\<flat> c \<triangleright> x. \<Q> x"
  by (simp add: pre_unicast_input_preservation)

lemma pre_broadcast_input_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x) \<Longrightarrow> \<star> \<triangleright> x. \<P> x \<preceq>\<^sub>\<flat> \<star> \<triangleright> x. \<Q> x"
proof (standard, (intro allI impI)+)
  assume "\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x"
  fix \<Gamma> and C
  assume "\<Gamma> \<turnstile> \<star> \<triangleright> x. \<P> x \<longmapsto>\<^sub>\<flat>C"
  then show "\<exists>D. \<Gamma> \<turnstile> \<star> \<triangleright> x. \<Q> x \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting op \<sim>\<^sub>\<flat> C D"
  proof cases
    case broadcast_input
    with `\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x` show ?thesis
      using basic_transition.broadcast_input and acting_lifting
      by (metis (no_types, lifting))
  qed (simp_all add: no_opening_transitions_from_broadcast_input)
qed

lemma broadcast_input_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<flat> \<Q> x) \<Longrightarrow> \<star> \<triangleright> x. \<P> x \<sim>\<^sub>\<flat> \<star> \<triangleright> x. \<Q> x"
  by (simp add: pre_broadcast_input_preservation)

inductive
  parallel_preservation_processes :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel: "
    P \<sim>\<^sub>\<flat> Q \<Longrightarrow> parallel_preservation_processes (P \<parallel> R) (Q \<parallel> R)" |
  with_new_channel: "
    (\<And>a. parallel_preservation_processes (\<S> a) (\<T> a)) \<Longrightarrow>
    parallel_preservation_processes (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

lemma parallel_preservation_processes_symmetry:
  "parallel_preservation_processes P Q \<Longrightarrow> parallel_preservation_processes Q P"
  by
    (induction rule: parallel_preservation_processes.induct)
    (simp_all add: parallel_preservation_processes.intros)

lemma parallel_preservation_processes_is_basic_simulation:
  "sim\<^sub>\<flat> parallel_preservation_processes"
proof (intro allI impI)+
  fix S and T and \<Gamma> and C
  assume "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C" and "parallel_preservation_processes S T"
  then show "\<exists>D. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting parallel_preservation_processes C D"
  proof (induction arbitrary: T)
    case (communication \<eta> \<mu> P P' R R' T)
    from communication.prems show ?case
    proof cases
      case (without_new_channel Q)
      from `P \<sim>\<^sub>\<flat> Q` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'` obtain Q' where "\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> Q'" and "P' \<sim>\<^sub>\<flat> Q'"
        using 
          basic_pre_bisimilarity.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          basic_residual_lifting.cases
        by smt
      from `\<eta> \<bowtie> \<mu>` and `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> Q'` and `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> R'` have "\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q' \<parallel> R'"
        by (intro basic_transition.communication)
      with `T = Q \<parallel> R` and `P' \<sim>\<^sub>\<flat> Q'` show ?thesis
        using parallel_preservation_processes.without_new_channel and acting_lifting
        by blast
    qed
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lifting
        by blast
    qed
  next
    case (acting_left P \<alpha> P' R T)
    from acting_left.prems show ?case
    proof cases
      case (without_new_channel Q)
      from `P \<sim>\<^sub>\<flat> Q` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P'` obtain Q' where "\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'" and "P' \<sim>\<^sub>\<flat> Q'"
        using 
          basic_pre_bisimilarity.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          basic_residual_lifting.cases
        by smt
      from `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'` have "\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<parallel> R"
        by (intro basic_transition.acting_left)
      with `T = Q \<parallel> R` and `P' \<sim>\<^sub>\<flat> Q'` show ?thesis
        using parallel_preservation_processes.without_new_channel and acting_lifting
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
          parallel_preservation_processes.without_new_channel and
          acting_lifting
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
          basic_pre_bisimilarity.cases and
          basic_residual.distinct(1) and
          basic_residual.inject(2) and
          basic_residual_lifting.cases
        by smt
      from `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a` have "\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<parallel> R"
        by (intro basic_transition.opening_left)
      with `T = Q \<parallel> R` and `\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a` show ?thesis
        using parallel_preservation_processes.without_new_channel and opening_lifting
        by (metis (no_types, lifting))
    qed
  next
    case (opening_right R \<R> P T)
    from opening_right.prems show ?case
    proof cases
      case (without_new_channel Q)
      from `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<R> a` have "\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q \<parallel> \<R> a"
        by (intro basic_transition.opening_right)
      from `P \<sim>\<^sub>\<flat> Q` have "\<And>a. parallel_preservation_processes (P \<parallel> \<R> a) (Q \<parallel> \<R> a)"
        by (intro parallel_preservation_processes.without_new_channel)
      with `T = Q \<parallel> R` and `\<Gamma> \<turnstile> Q \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q \<parallel> \<R> a` show ?thesis
        using opening_lifting
        by (metis (no_types, lifting))
    qed
  next
    case (scoped_acting S \<S>\<^sub>1 \<alpha> \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_acting S \<S>\<^sub>1
        with_new_channel: parallel_preservation_processes.with_new_channel)
  next
    case (scoped_opening S \<S>\<^sub>1 \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_opening S \<S>\<^sub>1
        with_new_channel: parallel_preservation_processes.with_new_channel)
  qed (blast elim: parallel_preservation_processes.cases)+
qed

lemma parallel_preservation_processes_is_basic_bisimulation:
  "bisim\<^sub>\<flat> parallel_preservation_processes"
  using
    parallel_preservation_processes_symmetry and
    parallel_preservation_processes_is_basic_simulation
  by (intro symmetric_basic_simulation)

lemma parallel_preservation: "P \<sim>\<^sub>\<flat> Q \<Longrightarrow> P \<parallel> R \<sim>\<^sub>\<flat> Q \<parallel> R"
proof -
  assume "P \<sim>\<^sub>\<flat> Q"
  then have "parallel_preservation_processes (P \<parallel> R) (Q \<parallel> R)"
    by (intro parallel_preservation_processes.without_new_channel)
  then show ?thesis
    using
      parallel_preservation_processes_is_basic_bisimulation and
      basic_bisimilarity_contains_all_basic_bisimulations
    by blast
qed

inductive
  new_channel_preservation_processes :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel: "
    P \<sim>\<^sub>\<flat> Q \<Longrightarrow> new_channel_preservation_processes P Q" |
  with_new_channel: "
    (\<And>a. new_channel_preservation_processes (\<S> a) (\<T> a)) \<Longrightarrow>
    new_channel_preservation_processes (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

lemma new_channel_preservation_processes_symmetry:
  "new_channel_preservation_processes P Q \<Longrightarrow> new_channel_preservation_processes Q P"
  by
    (induction rule: new_channel_preservation_processes.induct)
    (simp_all add: new_channel_preservation_processes.intros)

method new_channel_preservation_processes_trivial_transfer =
  (smt
    basic_pre_bisimilarity.cases
    new_channel_preservation_processes.without_new_channel
    basic_residual_lifting_monotonicity
    predicate2I
    predicate2D)

lemma new_channel_preservation_processes_is_basic_simulation:
  "sim\<^sub>\<flat> new_channel_preservation_processes"
proof (intro allI impI)+
  fix S and T and \<Gamma> and C
  assume "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C" and "new_channel_preservation_processes S T" and "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C"
  then show "\<exists>D. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting new_channel_preservation_processes C D"
  proof (induction (no_simp) arbitrary: T)
    case unicast_input
    from unicast_input.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case unicast_output
    from unicast_output.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case broadcast_input
    from broadcast_input.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case broadcast_output
    from broadcast_output.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case communication
    from communication.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lifting
        by blast
    qed new_channel_preservation_processes_trivial_transfer
  next
    case invocation
    from invocation.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case acting_left
    from acting_left.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case acting_right
    from acting_right.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case opening_left
    from opening_left.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case opening_right
    from opening_right.prems show ?case
      by cases new_channel_preservation_processes_trivial_transfer
  next
    case (scoped_acting S \<S>\<^sub>1 \<alpha> \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_acting S \<S>\<^sub>1
        with_new_channel: new_channel_preservation_processes.with_new_channel)
  next
    case (scoped_opening S \<S>\<^sub>1 \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_opening S \<S>\<^sub>1
        with_new_channel: new_channel_preservation_processes.with_new_channel)
  qed
qed

lemma new_channel_preservation_processes_is_basic_bisimulation:
  "bisim\<^sub>\<flat> new_channel_preservation_processes"
  using
    new_channel_preservation_processes_symmetry and
    new_channel_preservation_processes_is_basic_simulation
  by (intro symmetric_basic_simulation)

lemma new_channel_preservation: "(\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a) \<Longrightarrow> \<nu> a. \<P> a \<sim>\<^sub>\<flat> \<nu> a. \<Q> a"
proof -
  assume "\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a"
  then have "new_channel_preservation_processes (\<nu> a. \<P> a) (\<nu> a. \<Q> a)"
    by (simp add: new_channel_preservation_processes.intros)
  then show ?thesis
    using
      new_channel_preservation_processes_is_basic_bisimulation and
      basic_bisimilarity_contains_all_basic_bisimulations
    by blast
qed

inductive
  parallel_scope_extension_subprocesses :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel: "
    parallel_scope_extension_subprocesses Q P (P \<parallel> Q)" |
  with_new_channel: "
    (\<And>a. parallel_scope_extension_subprocesses Q (\<P> a) (\<R> a)) \<Longrightarrow>
    parallel_scope_extension_subprocesses Q (\<nu> a. \<P> a) (\<nu> a. \<R> a)"

method parallel_scope_extension_subprocesses_trivial_conveyance uses intro =
  (blast intro: intro parallel_scope_extension_subprocesses.without_new_channel)

method parallel_scope_extension_subprocesses_communication_conveyance =
  (parallel_scope_extension_subprocesses_trivial_conveyance intro: communication)

method parallel_scope_extension_subprocesses_acting_left_conveyance =
  (parallel_scope_extension_subprocesses_trivial_conveyance intro: acting_left)

method parallel_scope_extension_subprocesses_opening_left_conveyance =
  (parallel_scope_extension_subprocesses_trivial_conveyance intro: opening_left)

lemma parallel_scope_extension_subprocesses_opening_conveyance:
  assumes initial_relation: "parallel_scope_extension_subprocesses Q P T"
  assumes transition: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  shows "\<exists>\<T>. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T> a \<and> (\<forall>a. parallel_scope_extension_subprocesses Q (\<P> a) (\<T> a))"
using transition and initial_relation and transition
proof (induction (no_simp) P "\<lbrace>\<nu> a\<rbrace> \<P> a" arbitrary: \<P> T)
  case (opening \<P> \<P>' T)
  from opening.prems show ?case
  proof cases
    case with_new_channel
    with `\<lbrace>\<nu> a\<rbrace> \<P> a = \<lbrace>\<nu> a\<rbrace> \<P>' a` show ?thesis
      using basic_transition.opening
      by blast
  qed parallel_scope_extension_subprocesses_opening_left_conveyance
next
  case invocation
  from invocation.prems show ?case
    by cases parallel_scope_extension_subprocesses_opening_left_conveyance
next
  case opening_left
  from opening_left.prems show ?case
    by cases parallel_scope_extension_subprocesses_opening_left_conveyance
next
  case opening_right
  from opening_right.prems show ?case
    by cases parallel_scope_extension_subprocesses_opening_left_conveyance
next
  case (scoped_opening P \<P>\<^sub>1 \<P>\<^sub>2 \<P>' T)
  from
    scoped_opening.IH(1) and
    `parallel_scope_extension_subprocesses Q P T` and
    `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>\<^sub>1 a`
  obtain \<T>\<^sub>1 where
    "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
    "\<And>a. parallel_scope_extension_subprocesses Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)"
    by blast
  obtain \<T>\<^sub>2 where
    "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b" and
    "\<And>a b. parallel_scope_extension_subprocesses Q (\<P>\<^sub>2 a b) (\<T>\<^sub>2 a b)"
  proof -
    from
      scoped_opening.IH(2) and
      `\<And>a. parallel_scope_extension_subprocesses Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)` and
      `\<And>a. \<Gamma> \<turnstile> \<P>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<P>\<^sub>2 a b`
    have "
      \<forall>a. \<exists>\<H>.
      \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. parallel_scope_extension_subprocesses Q (\<P>\<^sub>2 a b) (\<H> b))"
      by blast
    then have "
      \<exists>\<T>\<^sub>2. \<forall>a.
      \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b \<and> (\<forall>b. parallel_scope_extension_subprocesses Q (\<P>\<^sub>2 a b) (\<T>\<^sub>2 a b))"
      by (intro choice)
    with that show ?thesis by blast
  qed
  from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<T>\<^sub>2 a b"
    by (intro basic_transition.scoped_opening)
  with
    `\<lbrace>\<nu> b\<rbrace> \<nu> a. \<P>\<^sub>2 a b = \<lbrace>\<nu> b\<rbrace> \<P>' b` and
    `\<And>a b. parallel_scope_extension_subprocesses Q (\<P>\<^sub>2 a b) (\<T>\<^sub>2 a b)`
  show ?case
    using basic_residual.inject(2) and parallel_scope_extension_subprocesses.with_new_channel
    by smt
qed simp_all

inductive
  parallel_scope_extension_processes :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel_ltr: "
    parallel_scope_extension_subprocesses Q P R \<Longrightarrow> parallel_scope_extension_processes (P \<parallel> Q) R" |
  without_new_channel_rtl: "
    parallel_scope_extension_subprocesses Q P R \<Longrightarrow> parallel_scope_extension_processes R (P \<parallel> Q)" |
  with_new_channel: "
    (\<And>a. parallel_scope_extension_processes (\<S> a) (\<T> a)) \<Longrightarrow>
    parallel_scope_extension_processes (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

lemma parallel_scope_extension_processes_symmetry:
  "parallel_scope_extension_processes P Q \<Longrightarrow> parallel_scope_extension_processes Q P"
  by
    (induction rule: parallel_scope_extension_processes.induct)
    (simp_all add: parallel_scope_extension_processes.intros)

lemma parallel_scope_extension_processes_without_new_channel_normalization:
  assumes "parallel_scope_extension_processes (P \<parallel> Q) T"
  shows "parallel_scope_extension_subprocesses Q P T"
using assms proof cases
  case without_new_channel_ltr
  then show ?thesis by simp
next
  case without_new_channel_rtl
  then show ?thesis
    using
      parallel_scope_extension_subprocesses.cases and
      parallel_scope_extension_subprocesses.without_new_channel
    by blast
qed

lemma parallel_scope_extension_processes_is_basic_simulation:
  "sim\<^sub>\<flat> parallel_scope_extension_processes"
proof (intro allI impI)+
  fix S and T and \<Gamma> and C
  assume "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C" and "parallel_scope_extension_processes S T"
  then show "\<exists>D. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting parallel_scope_extension_processes C D"
  proof (induction arbitrary: T)
    case (communication \<eta> \<mu> P P' Q Q' T)
    from communication.prems have "parallel_scope_extension_subprocesses Q P T"
      by (intro parallel_scope_extension_processes_without_new_channel_normalization)
    from `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'` and this and communication.hyps
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T' \<and> parallel_scope_extension_subprocesses Q' P' T'"
    proof (induction (no_simp) P "\<lbrace>IO \<eta>\<rbrace> P'" arbitrary: P' T)
      case unicast_input
      from unicast_input.prems show ?case
        by cases parallel_scope_extension_subprocesses_communication_conveyance
    next
      case unicast_output
      from unicast_output.prems show ?case
        by cases parallel_scope_extension_subprocesses_communication_conveyance
    next
      case broadcast_input
      from broadcast_input.prems show ?case
        by cases parallel_scope_extension_subprocesses_communication_conveyance
    next
      case broadcast_output
      from broadcast_output.prems show ?case
        by cases parallel_scope_extension_subprocesses_communication_conveyance
    next
      case invocation
      from invocation.prems show ?case
        by cases parallel_scope_extension_subprocesses_communication_conveyance
    next
      case acting_left
      from acting_left.prems show ?case
        by cases parallel_scope_extension_subprocesses_communication_conveyance
    next
      case acting_right
      from acting_right.prems show ?case
        by cases parallel_scope_extension_subprocesses_communication_conveyance
    next
      case (scoped_acting P \<P>\<^sub>1 \<beta> \<P>\<^sub>2 P' T)
      from `\<lbrace>\<beta>\<rbrace> \<nu> a. \<P>\<^sub>2 a = \<lbrace>IO \<eta>\<rbrace> P'` have "\<beta> = IO \<eta>" and "P' = \<nu> a. \<P>\<^sub>2 a"
        by simp_all
      from `parallel_scope_extension_subprocesses Q P T` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>\<^sub>1 a`
      obtain \<T>\<^sub>1 where
        "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
        "\<And>a. parallel_scope_extension_subprocesses Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)"
        using parallel_scope_extension_subprocesses_opening_conveyance
        by blast
      obtain \<T>\<^sub>2 where
        "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a" and
        "\<And>a. parallel_scope_extension_subprocesses Q' (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)"
      proof -
        from
          `\<beta> = IO \<eta>` and
          scoped_acting.IH(2) and
          `\<And>a. parallel_scope_extension_subprocesses Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)` and
          `\<eta> \<bowtie> \<mu>` and
          `\<And>a. \<Gamma> \<turnstile> \<P>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<beta>\<rbrace> \<P>\<^sub>2 a` and
          `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'`
        have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> H \<and> parallel_scope_extension_subprocesses Q' (\<P>\<^sub>2 a) H"
          by blast
        then have
          "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a \<and> parallel_scope_extension_subprocesses Q' (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)"
          by (intro choice)
        with that show ?thesis by blast
      qed
      from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
        by (intro basic_transition.scoped_acting)
      with `P' = \<nu> a. \<P>\<^sub>2 a` and `\<And>a. parallel_scope_extension_subprocesses Q' (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)`
      show ?case
        using parallel_scope_extension_subprocesses.with_new_channel
        by blast
    qed simp_all
    then show ?case
      using parallel_scope_extension_processes.without_new_channel_ltr and acting_lifting
      by blast
  next
    case (opening \<S> T)
    from opening.prems show ?case
    proof cases
      case (without_new_channel_rtl Q P)
      from `parallel_scope_extension_subprocesses Q P (\<nu> a. \<S> a)` show ?thesis
      proof cases
        case with_new_channel
        with `T = P \<parallel> Q` show ?thesis
          using
            basic_transition.opening and
            opening_left and
            parallel_scope_extension_processes.without_new_channel_rtl and
            opening_lifting
          by (metis (mono_tags, lifting))
      qed
    next
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lifting
        by blast
    qed
  next
    case (acting_left P \<alpha> P' Q T)
    from acting_left.prems have "parallel_scope_extension_subprocesses Q P T"
      by (intro parallel_scope_extension_processes_without_new_channel_normalization)
    from `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P'` and this and acting_left.hyps
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' \<and> parallel_scope_extension_subprocesses Q P' T'"
    proof (induction (no_simp) P "\<lbrace>\<alpha>\<rbrace> P'" arbitrary: P' T)
      case unicast_input
      from unicast_input.prems show ?case
        by cases parallel_scope_extension_subprocesses_acting_left_conveyance
    next
      case unicast_output
      from unicast_output.prems show ?case
        by cases parallel_scope_extension_subprocesses_acting_left_conveyance
    next
      case broadcast_input
      from broadcast_input.prems show ?case
        by cases parallel_scope_extension_subprocesses_acting_left_conveyance
    next
      case broadcast_output
      from broadcast_output.prems show ?case
        by cases parallel_scope_extension_subprocesses_acting_left_conveyance
    next
      case communication
      from communication.prems show ?case
        by cases parallel_scope_extension_subprocesses_acting_left_conveyance
    next
      case invocation
      from invocation.prems show ?case
        by cases parallel_scope_extension_subprocesses_acting_left_conveyance
    next
      case acting_left
      from acting_left.prems show ?case
        by cases parallel_scope_extension_subprocesses_acting_left_conveyance
    next
      case acting_right
      from acting_right.prems show ?case
        by cases parallel_scope_extension_subprocesses_acting_left_conveyance
    next
      case (scoped_acting P \<P>\<^sub>1 \<beta> \<P>\<^sub>2 P' T)
      from `\<lbrace>\<beta>\<rbrace> \<nu> a. \<P>\<^sub>2 a = \<lbrace>\<alpha>\<rbrace> P'` have "\<beta> = \<alpha>" and "P' = \<nu> a. \<P>\<^sub>2 a"
        by simp_all
      from `parallel_scope_extension_subprocesses Q P T` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>\<^sub>1 a`
      obtain \<T>\<^sub>1 where
        "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
        "\<And>a. parallel_scope_extension_subprocesses Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)"
        using parallel_scope_extension_subprocesses_opening_conveyance
        by blast
      obtain \<T>\<^sub>2 where
        "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a" and
        "\<And>a. parallel_scope_extension_subprocesses Q (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)"
      proof -
        from
          `\<beta> = \<alpha>` and
          scoped_acting.IH(2) and
          `\<And>a. parallel_scope_extension_subprocesses Q (\<P>\<^sub>1 a) (\<T>\<^sub>1 a)` and
          `\<And>a. \<Gamma> \<turnstile> \<P>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<beta>\<rbrace> \<P>\<^sub>2 a`
        have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> parallel_scope_extension_subprocesses Q (\<P>\<^sub>2 a) H"
          by blast
        then have
          "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a \<and> parallel_scope_extension_subprocesses Q (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)"
          by (intro choice)
        with that show ?thesis by blast
      qed
      from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
        by (intro basic_transition.scoped_acting)
      with `P' = \<nu> a. \<P>\<^sub>2 a` and `\<And>a. parallel_scope_extension_subprocesses Q (\<P>\<^sub>2 a) (\<T>\<^sub>2 a)`
      show ?case
        using parallel_scope_extension_subprocesses.with_new_channel
        by blast
    qed simp_all
    then show ?case
      using parallel_scope_extension_processes.without_new_channel_ltr and acting_lifting
      by blast
  next
    case (acting_right Q \<alpha> Q' P T)
    from acting_right.prems have "parallel_scope_extension_subprocesses Q P T"
      by (intro parallel_scope_extension_processes_without_new_channel_normalization)
    from this and acting_right.hyps
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' \<and> parallel_scope_extension_subprocesses Q' P T'"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.acting_right and
          parallel_scope_extension_subprocesses.without_new_channel
        by blast
    next
      case (with_new_channel Q \<P> \<T>)
      then have "
        \<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> parallel_scope_extension_subprocesses Q' (\<P> a) H"
        by simp
      then have "
        \<exists>\<T>'. \<forall>a. \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>' a \<and> parallel_scope_extension_subprocesses Q' (\<P> a) (\<T>' a)"
        by (intro choice)
      then show ?case
        using acting_scope and parallel_scope_extension_subprocesses.with_new_channel
        by metis
    qed
    then show ?case
      using parallel_scope_extension_processes.without_new_channel_ltr and acting_lifting
      by blast
  next
    case (opening_left P \<P> Q T)
    from opening_left.prems have "parallel_scope_extension_subprocesses Q P T"
      by (intro parallel_scope_extension_processes_without_new_channel_normalization)
    with opening_left.hyps show ?case
      using
        parallel_scope_extension_subprocesses_opening_conveyance and
        parallel_scope_extension_processes.without_new_channel_ltr and
        opening_lifting
      by (metis (no_types, lifting))
  next
    case (opening_right Q \<Q> P T)
    from opening_right.prems have "parallel_scope_extension_subprocesses Q P T"
      by (intro parallel_scope_extension_processes_without_new_channel_normalization)
    from this and opening_right.hyps
    have "\<exists>\<T>. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T> a \<and> (\<forall>a. parallel_scope_extension_subprocesses (\<Q> a) P (\<T> a))"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.opening_right and
          parallel_scope_extension_subprocesses.without_new_channel
        by blast
    next
      case (with_new_channel Q \<P> \<T>)
      then have "
        \<forall>a. \<exists>\<H>.
        \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. parallel_scope_extension_subprocesses (\<Q> b) (\<P> a) (\<H> b))"
        by simp
      then have "
        \<exists>\<T>'. \<forall>a.
        \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>' a b \<and> (\<forall>b. parallel_scope_extension_subprocesses (\<Q> b) (\<P> a) (\<T>' a b))"
        by (intro choice)
      then show ?case
        using opening_scope and parallel_scope_extension_subprocesses.with_new_channel
        by metis
    qed
    then show ?case
      using parallel_scope_extension_processes.without_new_channel_ltr and opening_lifting
      by (metis (no_types, lifting))
  next
    case (scoped_acting S \<S>\<^sub>1 \<alpha> \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_acting S \<S>\<^sub>1
        with_new_channel: parallel_scope_extension_processes.with_new_channel)
  next
    case (scoped_opening S \<S>\<^sub>1 \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_opening S \<S>\<^sub>1
        with_new_channel: parallel_scope_extension_processes.with_new_channel)
  qed (blast elim:
    parallel_scope_extension_subprocesses.cases
    parallel_scope_extension_processes.cases)+
qed

lemma parallel_scope_extension_processes_is_basic_bisimulation:
  "bisim\<^sub>\<flat> parallel_scope_extension_processes"
  using
    parallel_scope_extension_processes_symmetry and
    parallel_scope_extension_processes_is_basic_simulation
  by (intro symmetric_basic_simulation)

lemma parallel_scope_extension: "\<nu> a. \<P> a \<parallel> Q \<sim>\<^sub>\<flat> \<nu> a. (\<P> a \<parallel> Q)"
proof -
  have "parallel_scope_extension_processes (\<nu> a. \<P> a \<parallel> Q) (\<nu> a. (\<P> a \<parallel> Q))"
    by (simp add:
      parallel_scope_extension_subprocesses.intros
      parallel_scope_extension_processes.without_new_channel_ltr)
  then show ?thesis
    using
      parallel_scope_extension_processes_is_basic_bisimulation and
      basic_bisimilarity_contains_all_basic_bisimulations
    by blast
qed

lemma pre_new_channel_scope_extension: "\<nu> b. \<nu> a. \<P> a b \<preceq>\<^sub>\<flat> \<nu> a. \<nu> b. \<P> a b"
proof (standard, (intro allI impI)+)
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
  then show "\<exists>D. \<Gamma> \<turnstile> \<nu> a. \<nu> b. \<P> a b \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting op \<sim>\<^sub>\<flat> C D"
    using basic_bisimilarity_reflexivity and basic_residual_lifting_reflexivity
    by smt
qed

lemma new_channel_scope_extension: "\<nu> b. \<nu> a. \<P> a b \<sim>\<^sub>\<flat> \<nu> a. \<nu> b. \<P> a b"
  by (simp add: pre_new_channel_scope_extension)

inductive
  parallel_unit_processes :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel_ltr: "
    parallel_unit_processes (\<zero> \<parallel> P) P" |
  without_new_channel_rtl: "
    parallel_unit_processes P (\<zero> \<parallel> P)" |
  with_new_channel: "
    (\<And>a. parallel_unit_processes (\<S> a) (\<T> a)) \<Longrightarrow>
    parallel_unit_processes (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

lemma parallel_unit_processes_symmetry:
  "parallel_unit_processes P Q \<Longrightarrow> parallel_unit_processes Q P"
  by
    (induction rule: parallel_unit_processes.induct)
    (simp_all add: parallel_unit_processes.intros)

method parallel_unit_processes_trivial_transfer =
  (blast intro:
    acting_right
    opening_right
    parallel_unit_processes.without_new_channel_rtl
    basic_residual_lifting.intros)

lemma parallel_unit_processes_is_basic_simulation:
  "sim\<^sub>\<flat> parallel_unit_processes"
proof (intro allI impI)+
  fix S and T and \<Gamma> and C
  assume "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C" and "parallel_unit_processes S T" and "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C"
  then show "\<exists>D. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting parallel_unit_processes C D"
  proof (induction (no_simp) arbitrary: T)
    case unicast_input
    from unicast_input.prems show ?case
      by cases parallel_unit_processes_trivial_transfer
  next
    case unicast_output
    from unicast_output.prems show ?case
      by cases parallel_unit_processes_trivial_transfer
  next
    case broadcast_input
    from broadcast_input.prems show ?case
      by cases parallel_unit_processes_trivial_transfer
  next
    case broadcast_output
    from broadcast_output.prems show ?case
      by cases parallel_unit_processes_trivial_transfer
  next
    case communication
    from communication.prems show ?case
    proof cases
      case without_new_channel_ltr
      with communication.hyps show ?thesis
        by (simp add: no_transitions_from_stop)
    qed parallel_unit_processes_trivial_transfer
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lifting
        by blast
    qed parallel_unit_processes_trivial_transfer
  next
    case (invocation N V C T)
    from invocation.prems show ?case
      by (cases, cases C) parallel_unit_processes_trivial_transfer+
  next
    case acting_left
    from acting_left.prems show ?case
    proof cases
      case without_new_channel_ltr
      with acting_left.hyps show ?thesis
        by (simp add: no_transitions_from_stop)
    qed parallel_unit_processes_trivial_transfer
  next
    case acting_right
    from acting_right.prems show ?case
    proof cases
      case without_new_channel_ltr
      with acting_right.hyps show ?thesis
        using parallel_unit_processes.without_new_channel_ltr and acting_lifting
        by blast
    qed parallel_unit_processes_trivial_transfer
  next
    case opening_left
    from opening_left.prems show ?case
    proof cases
      case without_new_channel_ltr
      with opening_left.hyps show ?thesis
        by (simp add: no_transitions_from_stop)
    qed parallel_unit_processes_trivial_transfer
  next
    case opening_right
    from opening_right.prems show ?case
    proof cases
      case without_new_channel_ltr
      with opening_right.hyps show ?thesis
        using parallel_unit_processes.without_new_channel_ltr and opening_lifting
        by metis
    qed parallel_unit_processes_trivial_transfer
  next
    case (scoped_acting S \<S>\<^sub>1 \<alpha> \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_acting S \<S>\<^sub>1
        with_new_channel: parallel_unit_processes.with_new_channel)
  next
    case (scoped_opening S \<S>\<^sub>1 \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_opening S \<S>\<^sub>1
        with_new_channel: parallel_unit_processes.with_new_channel)
  qed
qed

lemma parallel_unit_processes_is_basic_bisimulation:
  "bisim\<^sub>\<flat> parallel_unit_processes"
  using
    parallel_unit_processes_symmetry and
    parallel_unit_processes_is_basic_simulation
  by (intro symmetric_basic_simulation)

lemma parallel_unit: "\<zero> \<parallel> P \<sim>\<^sub>\<flat> P"
proof -
  have "parallel_unit_processes (\<zero> \<parallel> P) P"
    by (intro parallel_unit_processes.without_new_channel_ltr)
  then show ?thesis
    using
      parallel_unit_processes_is_basic_bisimulation and
      basic_bisimilarity_contains_all_basic_bisimulations
    by blast
qed

inductive
  nested_parallel_commutativity_subprocesses :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel: "
    nested_parallel_commutativity_subprocesses R (P \<parallel> Q) ((P \<parallel> R) \<parallel> Q)" |
  with_new_channel: "
    (\<And>a. nested_parallel_commutativity_subprocesses R (\<U> a) (\<T> a)) \<Longrightarrow>
    nested_parallel_commutativity_subprocesses R (\<nu> a. \<U> a) (\<nu> a. \<T> a)"

lemma nested_parallel_commutativity_subprocesses_opening_conveyance:
  assumes initial_relation: "nested_parallel_commutativity_subprocesses R U T"
  assumes transition: "\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<U> a"
  shows "\<exists>\<T>. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T> a \<and> (\<forall>a. nested_parallel_commutativity_subprocesses R (\<U> a) (\<T> a))"
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
        nested_parallel_commutativity_subprocesses.without_new_channel
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
        nested_parallel_commutativity_subprocesses.without_new_channel
      by blast
  qed
next
  case (scoped_opening U \<U>\<^sub>1 \<U>\<^sub>2 T)
  from scoped_opening.hyps(2) and `nested_parallel_commutativity_subprocesses R U T`
  obtain \<T>\<^sub>1 where
    "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
    "\<And>a. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)"
    by blast
  obtain \<T>\<^sub>2 where
    "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b" and
    "\<And>a b. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>2 a b) (\<T>\<^sub>2 a b)"
  proof -
    from scoped_opening.hyps(4) and `\<And>a. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)`
    have "
      \<forall>a. \<exists>\<H>.
      \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>2 a b) (\<H> b))"
      by blast
    then have "
      \<exists>\<T>\<^sub>2. \<forall>a.
      \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b \<and> (\<forall>b. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>2 a b) (\<T>\<^sub>2 a b))"
      by (intro choice)
    with that show ?thesis by blast
  qed
  from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>\<^sub>2 a b` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<T>\<^sub>2 a b"
    by (intro basic_transition.scoped_opening)
  with `\<And>a b. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>2 a b) (\<T>\<^sub>2 a b)` show ?case
    using nested_parallel_commutativity_subprocesses.with_new_channel
    by metis
qed (blast elim: nested_parallel_commutativity_subprocesses.cases)

inductive
  nested_parallel_commutativity_processes :: "
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
where
  without_new_channel_ltr: "
    nested_parallel_commutativity_subprocesses R U T \<Longrightarrow>
    nested_parallel_commutativity_processes (U \<parallel> R) T" |
  without_new_channel_rtl: "
    nested_parallel_commutativity_subprocesses R U S \<Longrightarrow>
    nested_parallel_commutativity_processes S (U \<parallel> R)" |
  with_new_channel: "
    (\<And>a. nested_parallel_commutativity_processes (\<S> a) (\<T> a)) \<Longrightarrow>
    nested_parallel_commutativity_processes (\<nu> a. \<S> a) (\<nu> a. \<T> a)"

lemma nested_parallel_commutativity_processes_symmetry:
  "nested_parallel_commutativity_processes P Q \<Longrightarrow> nested_parallel_commutativity_processes Q P"
  by
    (induction rule: nested_parallel_commutativity_processes.induct)
    (simp_all add: nested_parallel_commutativity_processes.intros)

lemma nested_parallel_commutativity_processes_without_new_channel_normalization:
  assumes "nested_parallel_commutativity_processes (U \<parallel> R) T"
  shows "nested_parallel_commutativity_subprocesses R U T"
using assms proof cases
  case without_new_channel_ltr
  then show ?thesis by simp
next
  case without_new_channel_rtl
  then show ?thesis
    using
      nested_parallel_commutativity_subprocesses.cases and
      nested_parallel_commutativity_subprocesses.without_new_channel
    by blast
qed

lemma nested_parallel_commutativity_processes_is_basic_simulation:
  "sim\<^sub>\<flat> nested_parallel_commutativity_processes"
proof (intro allI impI)+
  fix S and T and \<Gamma> and C
  assume "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>C" and "nested_parallel_commutativity_processes S T"
  then show "\<exists>D. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>D \<and> basic_residual_lifting nested_parallel_commutativity_processes C D"
  proof (induction arbitrary: T)
    case (communication \<eta> \<mu> U U' R R' T)
    from communication.prems have "nested_parallel_commutativity_subprocesses R U T"
      by (intro nested_parallel_commutativity_processes_without_new_channel_normalization)
    with `\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> U'`
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T' \<and> nested_parallel_commutativity_subprocesses R' U' T'"
    proof (induction U "\<lbrace>IO \<eta>\<rbrace> U'" arbitrary: U' T)
      case (acting_left P P' Q T)
      from acting_left.prems show ?case
      proof cases
        case without_new_channel
        with `\<eta> \<bowtie> \<mu>` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'` and `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> R'` show ?thesis
          using
            basic_transition.communication and
            basic_transition.acting_left and
            nested_parallel_commutativity_subprocesses.without_new_channel
          by blast
      qed
    next
      case (acting_right Q Q' P T)
      from acting_right.prems show ?case
      proof cases
        case without_new_channel
        with `\<eta> \<bowtie> \<mu>` and `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> Q'` and `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> R'` show ?thesis
          using
            communication_symmetry and
            basic_transition.acting_right and
            basic_transition.communication and
            nested_parallel_commutativity_subprocesses.without_new_channel
          by blast
      qed
    next
      case (scoped_acting U \<U>\<^sub>1 \<U>\<^sub>2 T)
      from `nested_parallel_commutativity_subprocesses R U T` and `\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<U>\<^sub>1 a`
      obtain \<T>\<^sub>1 where
        "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
        "\<And>a. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)"
        using nested_parallel_commutativity_subprocesses_opening_conveyance
        by blast
      obtain \<T>\<^sub>2 where
        "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a" and
        "\<And>a. nested_parallel_commutativity_subprocesses R' (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)"
      proof -
        from
          scoped_acting.hyps(3) and
          `\<And>a. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)`
        have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> H \<and> nested_parallel_commutativity_subprocesses R' (\<U>\<^sub>2 a) H"
          by blast
        then have
          "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a \<and> nested_parallel_commutativity_subprocesses R' (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)"
          by (intro choice)
        with that show ?thesis by blast
      qed
      from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
        by (intro basic_transition.scoped_acting)
      with `\<And>a. nested_parallel_commutativity_subprocesses R' (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)`
      show ?case
        using nested_parallel_commutativity_subprocesses.with_new_channel
        by blast
    qed (blast elim: nested_parallel_commutativity_subprocesses.cases)+
    then show ?case
      using nested_parallel_commutativity_processes.without_new_channel_ltr and acting_lifting
      by blast
  next
    case (opening \<S> T)
    from opening.prems show ?case
    proof cases
      case (without_new_channel_rtl R U)
      from `nested_parallel_commutativity_subprocesses R U (\<nu> a. \<S> a)` show ?thesis
      proof cases
        case with_new_channel
        with `T = U \<parallel> R` show ?thesis
          using
            basic_transition.opening and
            opening_left and
            nested_parallel_commutativity_processes.without_new_channel_rtl and
            opening_lifting
          by (metis (mono_tags, lifting))
      qed
    next
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lifting
        by blast
    qed
  next
    case (acting_left U \<alpha> U' R T)
    from acting_left.prems have "nested_parallel_commutativity_subprocesses R U T"
      by (intro nested_parallel_commutativity_processes_without_new_channel_normalization)
    with `\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> U'`
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' \<and> nested_parallel_commutativity_subprocesses R U' T'"
    proof (induction U "\<lbrace>\<alpha>\<rbrace> U'" arbitrary: U' T)
      case (communication \<eta> \<mu> P P' Q Q' T)
      from communication.prems show ?case
      proof cases
        case without_new_channel
        with `\<tau> = \<alpha>` and `\<eta> \<bowtie> \<mu>` and `\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'` and `\<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'` show ?thesis
          using
            basic_transition.acting_left and
            basic_transition.communication and
            nested_parallel_commutativity_subprocesses.without_new_channel
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
            nested_parallel_commutativity_subprocesses.without_new_channel
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
            nested_parallel_commutativity_subprocesses.without_new_channel
          by blast
      qed
    next
      case (scoped_acting U \<U>\<^sub>1 \<U>\<^sub>2 T)
      from `nested_parallel_commutativity_subprocesses R U T` and `\<Gamma> \<turnstile> U \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<U>\<^sub>1 a`
      obtain \<T>\<^sub>1 where
        "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a" and
        "\<And>a. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)"
        using nested_parallel_commutativity_subprocesses_opening_conveyance
        by blast
      obtain \<T>\<^sub>2 where
        "\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a" and
        "\<And>a. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)"
      proof -
        from
          scoped_acting.hyps(3) and
          `\<And>a. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>1 a) (\<T>\<^sub>1 a)`
        have "\<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> nested_parallel_commutativity_subprocesses R (\<U>\<^sub>2 a) H"
          by blast
        then have
          "\<exists>\<T>\<^sub>2. \<forall>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a \<and> nested_parallel_commutativity_subprocesses R (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)"
          by (intro choice)
        with that show ?thesis by blast
      qed
      from `\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T>\<^sub>1 a` and `\<And>a. \<Gamma> \<turnstile> \<T>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>\<^sub>2 a` have "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<T>\<^sub>2 a"
        by (intro basic_transition.scoped_acting)
      with `\<And>a. nested_parallel_commutativity_subprocesses R (\<U>\<^sub>2 a) (\<T>\<^sub>2 a)`
      show ?case
        using nested_parallel_commutativity_subprocesses.with_new_channel
        by blast
    qed (blast elim: nested_parallel_commutativity_subprocesses.cases)+
    then show ?case
      using nested_parallel_commutativity_processes.without_new_channel_ltr and acting_lifting
      by blast
  next
    case (acting_right R \<alpha> R' U T)
    from acting_right.prems have "nested_parallel_commutativity_subprocesses R U T"
      by (intro nested_parallel_commutativity_processes_without_new_channel_normalization)
    from this and acting_right.hyps
    have "\<exists>T'. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' \<and> nested_parallel_commutativity_subprocesses R' U T'"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.acting_right and
          basic_transition.acting_left and
          nested_parallel_commutativity_subprocesses.without_new_channel
        by blast
    next
      case (with_new_channel R \<U> \<T>)
      then have "
        \<forall>a. \<exists>H. \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> H \<and> nested_parallel_commutativity_subprocesses R' (\<U> a) H"
        by simp
      then have "
        \<exists>\<T>'. \<forall>a. \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<T>' a \<and> nested_parallel_commutativity_subprocesses R' (\<U> a) (\<T>' a)"
        by (intro choice)
      then show ?case
        using acting_scope and nested_parallel_commutativity_subprocesses.with_new_channel
        by metis
    qed
    then show ?case
      using nested_parallel_commutativity_processes.without_new_channel_ltr and acting_lifting
      by blast
  next
    case (opening_left U \<U> R T)
    from opening_left.prems have "nested_parallel_commutativity_subprocesses R U T"
      by (intro nested_parallel_commutativity_processes_without_new_channel_normalization)
    with opening_left.hyps show ?case
      using
        nested_parallel_commutativity_subprocesses_opening_conveyance and
        nested_parallel_commutativity_processes.without_new_channel_ltr and
        opening_lifting
      by (metis (no_types, lifting))
  next
    case (opening_right R \<R> U T)
    from opening_right.prems have "nested_parallel_commutativity_subprocesses R U T"
      by (intro nested_parallel_commutativity_processes_without_new_channel_normalization)
    from this and opening_right.hyps
    have "\<exists>\<T>. \<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<T> a \<and> (\<forall>a. nested_parallel_commutativity_subprocesses (\<R> a) U (\<T> a))"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.opening_right and
          basic_transition.opening_left and
          nested_parallel_commutativity_subprocesses.without_new_channel
        by blast
    next
      case (with_new_channel R \<U> \<T>)
      then have "
        \<forall>a. \<exists>\<H>.
        \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<H> b \<and> (\<forall>b. nested_parallel_commutativity_subprocesses (\<R> b) (\<U> a) (\<H> b))"
        by simp
      then have "
        \<exists>\<T>'. \<forall>a.
        \<Gamma> \<turnstile> \<T> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<T>' a b \<and> (\<forall>b. nested_parallel_commutativity_subprocesses (\<R> b) (\<U> a) (\<T>' a b))"
        by (intro choice)
      then show ?case
        using opening_scope and nested_parallel_commutativity_subprocesses.with_new_channel
        by metis
    qed
    then show ?case
      using nested_parallel_commutativity_processes.without_new_channel_ltr and opening_lifting
      by (metis (no_types, lifting))
  next
    case (scoped_acting S \<S>\<^sub>1 \<alpha> \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_acting S \<S>\<^sub>1
        with_new_channel: nested_parallel_commutativity_processes.with_new_channel)
  next
    case (scoped_opening S \<S>\<^sub>1 \<S>\<^sub>2 T)
    then show ?case
      by (is_simulation_scoped_opening S \<S>\<^sub>1
        with_new_channel: nested_parallel_commutativity_processes.with_new_channel)
  qed (blast elim:
    nested_parallel_commutativity_subprocesses.cases
    nested_parallel_commutativity_processes.cases)+
qed

lemma nested_parallel_commutativity_processes_is_basic_bisimulation:
  "bisim\<^sub>\<flat> nested_parallel_commutativity_processes"
  using
    nested_parallel_commutativity_processes_symmetry and
    nested_parallel_commutativity_processes_is_basic_simulation
  by (intro symmetric_basic_simulation)

lemma nested_parallel_commutativity: "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>\<flat> (P \<parallel> R) \<parallel> Q"
proof -
  have "nested_parallel_commutativity_processes ((P \<parallel> Q) \<parallel> R) ((P \<parallel> R) \<parallel> Q)"
    by (simp add:
      nested_parallel_commutativity_subprocesses.without_new_channel
      nested_parallel_commutativity_processes.without_new_channel_ltr)
  then show ?thesis
    using
      nested_parallel_commutativity_processes_is_basic_bisimulation and
      basic_bisimilarity_contains_all_basic_bisimulations
    by blast
qed

lemma parallel_commutativity: "P \<parallel> Q \<sim>\<^sub>\<flat> Q \<parallel> P"
proof -
  have "P \<parallel> Q \<sim>\<^sub>\<flat> (\<zero> \<parallel> P) \<parallel> Q" using parallel_unit and parallel_preservation by blast
  also have "(\<zero> \<parallel> P) \<parallel> Q \<sim>\<^sub>\<flat> (\<zero> \<parallel> Q) \<parallel> P" by (intro nested_parallel_commutativity)
  also have "(\<zero> \<parallel> Q) \<parallel> P \<sim>\<^sub>\<flat> Q \<parallel> P" using parallel_unit and parallel_preservation by blast
  finally show ?thesis .
qed

lemma parallel_associativity: "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>\<flat> P \<parallel> (Q \<parallel> R)"
proof -
  have "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>\<flat> (Q \<parallel> P) \<parallel> R" using parallel_commutativity and parallel_preservation by blast
  also have "(Q \<parallel> P) \<parallel> R \<sim>\<^sub>\<flat> (Q \<parallel> R) \<parallel> P" by (intro nested_parallel_commutativity)
  also have "(Q \<parallel> R) \<parallel> P \<sim>\<^sub>\<flat> P \<parallel> (Q \<parallel> R)" by (intro parallel_commutativity)
  finally show ?thesis .
qed

end
