theory Basic_Weak_Bisimulation
  imports Typed_Basic_Transition_System
begin

(* Sequence of \<tau>-transitions: \<Longrightarrow>\<^sub>\<flat> *)

abbreviation tau_sequence :: "process \<Rightarrow> process \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat>" 50)
where
  "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<equiv> (P, Q) \<in> {(P, Q) | P Q. P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q}^*"

lemma tau_sequence_refl: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P"
  by simp

lemma tau_sequence_non_empty: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q; P \<noteq> Q \<rbrakk> \<Longrightarrow> \<exists>R. P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R \<and> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (smt Pair_inject converse_rtranclE mem_Collect_eq)

lemma tau_sequence_trans: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by simp

lemma tau_transition_is_tau_sequence: "P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by auto

lemma append_tau_transition_to_tau_sequence_is_tau_sequence:  "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (metis (mono_tags, lifting) mem_Collect_eq rtrancl.simps)

lemma prepend_tau_transition_to_tau_sequence_is_tau_sequence: "\<lbrakk> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R; R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (simp add: rtrancl_into_trancl2 trancl_into_rtrancl)

lemma tau_sequence_induction[consumes 1, case_names tau_seq_refl tau_seq_step]:
  assumes "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  and     "Prop P"
  and     "\<And>R S. \<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S; Prop R \<rbrakk> \<Longrightarrow> Prop S"
  shows   "Prop Q"
  using assms
  by (induction rule: rtrancl_induct) auto

(* The lifted operational semantics rules for \<tau>-sequences. *)
(* \<tau>-sequence relation behaves as expected w.r.t. process operators (except, of course, \<triangleright> and \<triangleleft>) *)

lemma tau_sequence_parallel_preservation_left: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R P')
  then have "R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q"
    using tau_seq_step.hyps(2) by (simp add: acting_left)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_parallel_preservation_right: "Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q' \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> Q'"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R Q')
  then have "P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P \<parallel> Q'"
    using tau_seq_step.hyps(2) by (simp add: acting_right)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_parallel_preservation: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'; Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q' \<rbrakk> \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'"
proof -
  assume "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'" and "Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
  have "P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
    using \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> and tau_sequence_parallel_preservation_left by simp
  moreover have "P' \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'"
    using \<open>Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> and tau_sequence_parallel_preservation_right by simp
  finally show ?thesis
    by simp
qed

lemma tau_sequence_new_channel_preservation: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<Longrightarrow> \<nu> a. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<nu> a. Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R P')
  then have "\<nu> a. R  \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. P'"
    using tau_seq_step(2) by (simp add: acting_scope)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

(* Weak Semantics *)

(** Weak \<tau>-respecting basic transition \<Longrightarrow>\<^sub>\<flat>C **)
(** NOTE: Note that even though the transition P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a appears to contain a binder into \<Q> a, in
reality it does not. The binder occurs inside the definition, where a binds into \<P> a. The process
\<P> a then does a \<tau>-sequence to \<Q> a, which "a" does not bind into, unless \<P> a = \<Q> a. Formally, one can
still reason about "a" as a binder: there is no way that any new names can be introduced by a \<tau>-sequence;
the name "a" can be communicated within the process, but if so it occurs free in an output-prefix in P. **)
(** TODO: Perhaps I can define a weak basic transition without using a residual, i.e. as
 weak_tau_respecting_basic_transition :: process \<Rightarrow> process \<Rightarrow> [IO action|chan] \<Rightarrow> process **)

definition
  weak_tau_respecting_basic_transition :: "process \<Rightarrow> basic_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<flat>" 50)
  where
   "P \<Longrightarrow>\<^sub>\<flat>C \<equiv>
      case C of
        \<lbrace>\<alpha>\<rbrace> Q     \<Rightarrow> \<exists>R S. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<and> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q |
        Opening \<Q> \<Rightarrow> \<exists>R \<P>. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a)"

lemma weak_tau_respecting_basic_transition_acting_intro: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S; S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  using weak_tau_respecting_basic_transition_def by force

lemma weak_tau_respecting_basic_transition_opening_intro: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a; \<And>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  using weak_tau_respecting_basic_transition_def by force

lemma weak_tau_respecting_basic_transition_acting_elim: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<exists>R S. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<and> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (simp split: basic_residual.split add: weak_tau_respecting_basic_transition_def)

lemma weak_tau_respecting_basic_transition_opening_elim: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<exists>R \<P>. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a)"
  by (simp split: basic_residual.split add: weak_tau_respecting_basic_transition_def)

lemma weak_tau_respecting_basic_transition_single_acting: "P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  using weak_tau_respecting_basic_transition_acting_intro by blast

lemma weak_tau_respecting_basic_transition_single_opening: "P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  using weak_tau_respecting_basic_transition_opening_intro by blast

lemma weak_tau_respecting_basic_transition_tau: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q"
  then obtain R and S where "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S" and "S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" using \<open>R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S\<close> and tau_transition_is_tau_sequence by simp
  then show ?thesis using \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> by (simp add: tau_sequence_trans)
qed

lemma prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  then obtain S and T where "R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" and "S \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T" and "T \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" using \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>S \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<close> and \<open>T \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma prepend_tau_sequence_to_weak_tau_respecting_basic_transition_opening: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
proof -
  assume "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then obtain S and \<P> where "R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" and "S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" and "\<forall>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a" using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" using \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a\<close> and \<open>\<forall>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a\<close> by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

lemma append_tau_sequence_to_weak_tau_respecting_basic_transition_acting: "\<lbrakk> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R; R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R" and "R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  then obtain S and T where "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" and "S \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T" and "T \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "T \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" using \<open>R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> and \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>S \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<close> and \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma append_tau_sequence_to_weak_tau_respecting_basic_transition_opening: "\<lbrakk> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a; \<And>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
proof -
  assume "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" and "\<And>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a"
  then obtain S and \<S> where "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" and "S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<S> a" and "\<forall>a. \<S> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a" using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "\<And>a. \<S> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a" using \<open>\<And>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a\<close> and \<open>\<forall>a. \<S> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> using tau_sequence_trans by fastforce
  then show ?thesis using \<open>S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<S> a\<close> and \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> using weak_tau_respecting_basic_transition_opening_intro by fastforce
qed

(** Lifted weak \<tau>-respecting basic operational semantics **)

lemma weak_tau_respecting_basic_transition_sending: "c \<triangleleft> V \<Longrightarrow>\<^sub>\<flat>\<lbrace>c \<triangleleft> V\<rbrace> \<zero>"
  using weak_tau_respecting_basic_transition_def and sending by force

lemma weak_tau_respecting_basic_transition_receiving: "c \<triangleright> x. \<P> x \<Longrightarrow>\<^sub>\<flat>\<lbrace>c \<triangleright> V\<rbrace> \<P> V"
  using weak_tau_respecting_basic_transition_def and receiving by force

lemma weak_tau_respecting_basic_transition_communication: "\<lbrakk> \<eta> \<bowtie> \<mu>; P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'; Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q' \<rbrakk> \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'"
proof -
  assume "\<eta> \<bowtie> \<mu>" and "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'" and "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'"
  then obtain R and S where "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> S" and "S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'"
    using weak_tau_respecting_basic_transition_acting_elim and \<open>P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'\<close> by fastforce
  moreover obtain T and U where "Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> T" and "T \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> U" and "U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
    using weak_tau_respecting_basic_transition_acting_elim and \<open>Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'\<close> by fastforce
  ultimately show ?thesis
  proof -
    have "R \<parallel> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S \<parallel> U"
      using \<open>\<eta> \<bowtie> \<mu>\<close> and \<open>R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> S\<close> and \<open>T \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> U\<close> using communication by fastforce
    moreover have "P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> T"
      using \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> T\<close> and tau_sequence_parallel_preservation by simp
    moreover have "S \<parallel> U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'"
      using \<open>S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> and \<open>U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> and tau_sequence_parallel_preservation by simp
    ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'"
      using weak_tau_respecting_basic_transition_acting_intro by simp
  qed
qed

lemma weak_tau_respecting_basic_transition_opening: "\<nu> a. \<P> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  by (simp add: opening weak_tau_respecting_basic_transition_single_opening)

lemma weak_tau_respecting_basic_transition_acting_left: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P' \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P' \<parallel> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P'"
  then obtain R and S where "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S" and "S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> Q"
    using tau_sequence_parallel_preservation and \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<parallel> Q"
    using acting_left and \<open>R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> by fastforce
  moreover have "S \<parallel> Q  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
    using tau_sequence_parallel_preservation_left and \<open>S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> by simp
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma weak_tau_respecting_basic_transition_acting_right: "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P \<parallel> Q'"
proof -
  assume "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'"
  then obtain R and S where "Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S" and "S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> R"
    using tau_sequence_parallel_preservation and \<open>Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P \<parallel> S"
    using acting_right and \<open>R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> by fastforce
  moreover have "P \<parallel> S  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> Q'"
    using tau_sequence_parallel_preservation_right and \<open>S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> by simp
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma weak_tau_respecting_basic_transition_opening_left: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<parallel> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  then obtain R and \<Q> where "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" and "\<forall>a. \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a"
    using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> Q"
    using tau_sequence_parallel_preservation and \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<parallel> Q"
    using opening_left and \<open>R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close> by fastforce
  moreover have "\<And>a. \<Q> a \<parallel> Q  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a \<parallel> Q"
    using tau_sequence_parallel_preservation_left and \<open>\<forall>a. \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> by fastforce
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

lemma weak_basic_transition_opening_right: "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P \<parallel> \<Q> a"
proof -
  assume "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then obtain R and \<P> where "Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" and "\<forall>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a"
    using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> R"
    using tau_sequence_parallel_preservation and \<open>Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P \<parallel> \<P> a"
    using opening_right and \<open>R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a\<close> by fastforce
  moreover have "\<And>a. P \<parallel> \<P> a  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> \<Q> a"
    using tau_sequence_parallel_preservation_right and \<open>\<forall>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a\<close> by fastforce
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

(* TODO: Prove. *)
lemma weak_tau_respecting_basic_transition_scoped_acting: "\<lbrakk> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Q> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<R> a \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<R> a"
  sorry

(* TODO: Prove. *)
lemma weak_tau_respecting_basic_transition_scoped_opening: "\<lbrakk> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Q> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<R> a b \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<R> a b"
  sorry

(** Weak basic transition \<Longrightarrow>\<^sub>\<flat>\<^sup>^ **)

definition weak_basic_transition :: "process \<Rightarrow> basic_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<flat>\<^sup>^" 50)
  where
   "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^C \<equiv>
      case C of
        \<lbrace>\<alpha>\<rbrace> Q \<Rightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<or> (\<alpha> = \<tau> \<and> P = Q) |
        Opening \<Q> \<Rightarrow> P \<Longrightarrow>\<^sub>\<flat> Opening \<Q>"

lemma prepend_tau_transition_to_weak_basic_transition: "\<lbrakk> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R; R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R" and "R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  then have "R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<or> \<alpha> = \<tau> \<and> R = Q"
    by (simp add: weak_basic_transition_def)
  then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<or> \<alpha> = \<tau> \<and> P = Q"
    using \<open>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R\<close> and prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting and weak_tau_respecting_basic_transition_single_acting by blast
  then show ?thesis
    by (simp add: weak_basic_transition_def)
qed

lemma append_tau_transition_to_weak_basic_transition: "\<lbrakk> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R; R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q" and "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R"
  then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R \<or> \<alpha> = \<tau> \<and> P = R"
    by (simp add: weak_basic_transition_def)
  then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<or> \<alpha> = \<tau> \<and> P = Q"
    using \<open>R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q\<close> and append_tau_sequence_to_weak_tau_respecting_basic_transition_acting and weak_tau_respecting_basic_transition_single_acting by blast
  then show ?thesis
    by (simp add: weak_basic_transition_def)
qed

lemma tau_sequence_is_weak_basic_tau_transition: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by (simp add: weak_basic_transition_def)
next
  case (tau_seq_step R S)
  then show ?case by (simp add: append_tau_transition_to_weak_basic_transition)
qed

lemma weak_basic_tau_transition_is_tau_sequence: "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> Q"
  then show ?thesis
  proof (cases "P = Q")
    case True
    then show ?thesis by (simp add: tau_sequence_refl)
  next
    case False
    then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q" using \<open>P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> Q\<close> and weak_basic_transition_def by force
    then show ?thesis using weak_tau_respecting_basic_transition_tau by fastforce
  qed
qed

lemma weak_basic_transition_refl_intro: "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> P"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_step_intro: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_step_elim: "\<lbrakk> P \<noteq> Q; P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_induction
  [consumes 1, case_names weak_basic_tran_refl weak_basic_tran_step]:
  assumes "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  and     "Prop \<tau> P"
  and     "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> Prop \<alpha> Q"
  shows   "Prop \<alpha> Q"
  using assms
  by (auto simp add: weak_basic_transition_def)

lemma weak_basic_transition_single_acting: "P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  using weak_tau_respecting_basic_transition_acting_intro and weak_basic_transition_step_intro by fastforce

lemma prepend_tau_sequence_to_weak_basic_transition: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  then show ?thesis
  proof (cases "R = Q")
    case True
    then have A1: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" using \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and True by simp
    moreover have A2: "Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q" using \<open>R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<alpha> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_basic_tau_transition)
    next
      case False
      then have "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using A2 and False by (simp add: weak_basic_transition_def)
      then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using A1 by (simp add: prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting)
      then show ?thesis by (simp add: weak_basic_transition_step_intro)
    qed
  next
    case False
    then have "R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using \<open>R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q\<close> by (simp add: weak_basic_transition_step_elim)
    then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using \<open>P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting by simp
    then show ?thesis by (simp add: weak_basic_transition_step_intro)
  qed
qed

lemma append_tau_sequence_to_weak_basic_transition: "\<lbrakk> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R; R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R" and "R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  then show ?thesis
  proof (cases "P = R")
    case True
    then have A1: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" using \<open>R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> and True by simp
    moreover have A2: "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P" using \<open>P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<alpha> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_basic_tau_transition)
    next
      case False
      then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P" using A2 and False by (simp add: weak_basic_transition_def)
      then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using A1 by (simp add: append_tau_sequence_to_weak_tau_respecting_basic_transition_acting)
      then show ?thesis by (simp add: weak_basic_transition_step_intro)
    qed
  next
    case False
    then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R" using \<open>P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R\<close> by (simp add: weak_basic_transition_step_elim)
    then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using \<open>R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> and append_tau_sequence_to_weak_tau_respecting_basic_transition_acting by simp
    then show ?thesis by (simp add: weak_basic_transition_step_intro)
  qed
qed

(** Lifted weak basic operational semantics **)

lemma weak_basic_transition_sending: "c \<triangleleft> V \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>c \<triangleleft> V\<rbrace> \<zero>"
  by (simp add: weak_tau_respecting_basic_transition_sending weak_basic_transition_def)

lemma weak_basic_transition_receiving: "c \<triangleright> x. \<P> x \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>c \<triangleright> V\<rbrace> \<P> V"
  by (simp add: weak_tau_respecting_basic_transition_receiving weak_basic_transition_def)

lemma weak_basic_transition_communication: "\<lbrakk> \<eta> \<bowtie> \<mu>; P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>IO \<eta>\<rbrace> P'; Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>IO \<mu>\<rbrace> Q' \<rbrakk> \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'"
  by (simp add: weak_tau_respecting_basic_transition_communication weak_basic_transition_def)

lemma weak_basic_transition_acting_left: "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<parallel> Q"
  by (auto simp add: weak_tau_respecting_basic_transition_acting_left weak_basic_transition_def)

lemma weak_basic_transition_acting_right: "Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q' \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P \<parallel> Q'"
  by (auto simp add: weak_tau_respecting_basic_transition_acting_right weak_basic_transition_def)

(* Weak basic bisimilarity *)

(** Weak basic simulation **)

definition weak_basic_simulation :: "process \<Rightarrow> (process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> process \<Rightarrow> bool"
  ("_ \<leadsto>\<^sub>\<flat><_> _" [50, 50, 50] 50)
  where
    "P \<leadsto>\<^sub>\<flat><\<X>> Q \<equiv>
      (\<forall>\<alpha> Q'. Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<longrightarrow> (\<exists>P'. P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'))
      \<and>
      (\<forall>\<Q>. Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<longrightarrow> (\<exists>\<P>. P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<X> (\<P> a) (\<Q> a))))"

abbreviation
  is_weak_basic_sim
where
  "is_weak_basic_sim \<X> \<equiv> \<forall>P Q. \<X> P Q \<longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> Q"

lemma weak_basic_sim_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> Q \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<Y>> Q"
  by (simp add: weak_basic_simulation_def) blast

lemma weak_basic_sim_cases
  [case_names acting opening]:
  assumes acting:  "\<And>\<alpha> Q'. Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'"
  and     opening: "\<And>\<Q>. Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<exists>\<P>. P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<X> (\<P> a) (\<Q> a))"
  shows            "P \<leadsto>\<^sub>\<flat><\<X>> Q"
  using assms
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_acting_elim: "\<lbrakk> P \<leadsto>\<^sub>\<flat><\<X>> Q; Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<rbrakk> \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'"
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_opening_elim: "\<lbrakk> P \<leadsto>\<^sub>\<flat><\<X>> Q; Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<rbrakk> \<Longrightarrow> \<exists>\<P>. P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<X> (\<P> a) (\<Q> a))"
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_reflexivity: "(\<And>P. \<X> P P) \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> P"
  using weak_basic_simulation_def weak_basic_transition_single_acting weak_tau_respecting_basic_transition_single_opening by blast

lemma weak_basic_sim_tau_sequence:
  assumes A\<^sub>1: "Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
  and     A\<^sub>2: "\<X> P Q"
  and     A\<^sub>3: "is_weak_basic_sim \<X>"
  shows       "\<exists>P'. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<and> \<X> P' Q'"
  using assms
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  moreover have "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P" by simp
  ultimately show ?case using A\<^sub>3 and A\<^sub>2 by blast
next
  case (tau_seq_step Q' Q'')
  have "\<exists>P'. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<and> \<X> P' Q'" using tau_seq_step.prems and tau_seq_step.IH by simp
  then obtain P' where A\<^sub>4: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'" and A\<^sub>5: "\<X> P' Q'" by auto
  then have "P' \<leadsto>\<^sub>\<flat><\<X>> Q'" using A\<^sub>5 and A\<^sub>3 by simp
  moreover have A\<^sub>6: "Q' \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q''" by fact
  ultimately obtain P'' where A\<^sub>7: "P' \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> P''" and A\<^sub>8: "\<X> P'' Q''" by (blast dest: weak_basic_sim_acting_elim)
  then have "P' \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P''" using A\<^sub>7 and weak_basic_tau_transition_is_tau_sequence by blast
  then have "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P''" using A\<^sub>4 by simp
  then show ?case using A\<^sub>8 by auto
qed

(* TODO: Prove it. *)
lemma weak_basic_sim_tau_sequence2:
  assumes A\<^sub>1: "\<And>a. \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q>' a"
  and     A\<^sub>2: "\<And>a. \<X> (\<P> a) (\<Q> a)"
  and     A\<^sub>3: "is_weak_basic_sim \<X>"
  shows       "\<exists>\<P>'. \<forall>a. \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P>' a \<and> \<X> (\<P>' a) (\<Q>' a)"
  sorry

lemma weak_basic_sim_acting_elim2:
  assumes A\<^sub>1: "is_weak_basic_sim \<X>"
  and     A\<^sub>2: "\<X> P Q"
  and     A\<^sub>3: "Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q'"
  shows       "\<exists>P'. P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'"
  using assms
proof -
  assume "Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q'"
  then show "\<exists>P'. P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'"
  proof (induction rule: weak_basic_transition_induction)
    case weak_basic_tran_refl
    then have "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> P" by (simp add: weak_basic_transition_refl_intro)
    then show ?case using A\<^sub>2 by auto
  next
    case weak_basic_tran_step
    have "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'" by fact
    then obtain Q\<^sub>2 and Q\<^sub>3 where A\<^sub>4: "Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<^sub>2" and A\<^sub>5: "Q\<^sub>2 \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q\<^sub>3" and A\<^sub>6: "Q\<^sub>3 \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
      by (blast dest: weak_tau_respecting_basic_transition_acting_elim)
    then have "\<exists>P\<^sub>2. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<^sub>2 \<and> \<X> P\<^sub>2 Q\<^sub>2" using A\<^sub>4 and A\<^sub>2 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
    then obtain P\<^sub>2 where A\<^sub>7: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<^sub>2" and A\<^sub>8: "\<X> P\<^sub>2 Q\<^sub>2" by auto
    then have "P\<^sub>2 \<leadsto>\<^sub>\<flat><\<X>> Q\<^sub>2" using A\<^sub>8 and A\<^sub>1 by simp
    then obtain P\<^sub>3 where A\<^sub>9: "P\<^sub>2 \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P\<^sub>3" and A\<^sub>1\<^sub>0: "\<X> P\<^sub>3 Q\<^sub>3" using A\<^sub>5 by (blast dest: weak_basic_sim_acting_elim)
    then have "\<exists>P'. P\<^sub>3 \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<and> \<X> P' Q'" using A\<^sub>6 and A\<^sub>1\<^sub>0 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
    then obtain P' where A\<^sub>1\<^sub>1: "P\<^sub>3 \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'" and A\<^sub>1\<^sub>2: "\<X> P' Q'" by auto
    then have "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P'" using A\<^sub>7 and A\<^sub>9 and A\<^sub>1\<^sub>1
      by (blast dest: prepend_tau_sequence_to_weak_basic_transition append_tau_sequence_to_weak_basic_transition)
    then show ?case using A\<^sub>1\<^sub>2 by auto
  qed
qed

lemma weak_basic_sim_opening_elim2:
  assumes A\<^sub>1: "is_weak_basic_sim \<X>"
  and     A\<^sub>2: "\<X> P Q"
  and     A\<^sub>3: "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  shows       "\<exists>\<P>. P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<X> (\<P> a) (\<Q> a))"
  using assms
proof -
  assume "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then obtain Q\<^sub>2 and \<Q>\<^sub>3 where A\<^sub>4: "Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<^sub>2" and A\<^sub>5: "Q\<^sub>2 \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q>\<^sub>3 a" and A\<^sub>6: "\<forall>a. \<Q>\<^sub>3 a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a"
    by (blast dest: weak_tau_respecting_basic_transition_opening_elim)
  then have "\<exists>P\<^sub>2. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<^sub>2 \<and> \<X> P\<^sub>2 Q\<^sub>2" using A\<^sub>4 and A\<^sub>2 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
  then obtain P\<^sub>2 where A\<^sub>7: "P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<^sub>2" and A\<^sub>8: "\<X> P\<^sub>2 Q\<^sub>2" by auto
  then have "P\<^sub>2 \<leadsto>\<^sub>\<flat><\<X>> Q\<^sub>2" using A\<^sub>8 and A\<^sub>1 by simp
  then obtain \<P>\<^sub>3 where A\<^sub>9: "P\<^sub>2 \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>\<^sub>3 a" and A\<^sub>1\<^sub>0: "\<forall>a. \<X> (\<P>\<^sub>3 a) (\<Q>\<^sub>3 a)" using A\<^sub>5
    by (blast dest: weak_basic_sim_opening_elim)
  then have "\<exists>\<P>. \<forall>a. \<P>\<^sub>3 a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a \<and> \<X> (\<P> a) (\<Q> a)" using A\<^sub>6 and A\<^sub>1\<^sub>0 and A\<^sub>1 weak_basic_sim_tau_sequence2 by blast
  then obtain \<P> where A\<^sub>1\<^sub>1: "\<And>a. \<P>\<^sub>3 a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a" and A\<^sub>1\<^sub>2: "\<And>a. \<X> (\<P> a) (\<Q> a)" by auto
  then have "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" using A\<^sub>7 and A\<^sub>9 and A\<^sub>1\<^sub>1
    by (blast dest: prepend_tau_sequence_to_weak_tau_respecting_basic_transition_opening append_tau_sequence_to_weak_tau_respecting_basic_transition_opening)
  then show ?thesis using A\<^sub>1\<^sub>2 by auto
qed

lemma weak_basic_sim_transitivity:
  assumes A\<^sub>1: "Q \<leadsto>\<^sub>\<flat><\<Y>> R"
  and     A\<^sub>2: "\<X> OO \<Y> \<le> \<Z>"
  and     A\<^sub>3: "is_weak_basic_sim \<X>"
  and     A\<^sub>4: "\<X> P Q"
  shows "P \<leadsto>\<^sub>\<flat><\<Z>> R"
  using assms
proof -
  show ?thesis
  proof (induction rule: weak_basic_sim_cases)
    case (acting \<alpha> Q')
    then have "R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'" by simp
    then obtain Q\<^sub>2 where A\<^sub>5: "Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q\<^sub>2" and A\<^sub>6: "\<Y> Q\<^sub>2 Q'" using A\<^sub>1 by (blast dest: weak_basic_sim_acting_elim)
    then have "\<exists>P'. P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q\<^sub>2" using A\<^sub>3 and A\<^sub>4 and A\<^sub>5 by (blast intro: weak_basic_sim_acting_elim2)
    then obtain P' where A\<^sub>7: "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P'" and A\<^sub>8: "\<X> P' Q\<^sub>2" by auto
    then have "\<Z> P' Q'" using A\<^sub>8 and A\<^sub>6 and A\<^sub>2 by auto
    then show ?case using A\<^sub>7 by auto
  next
    case (opening \<Q>)
    then have "R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" by simp
    then obtain \<Q>' where A\<^sub>9: "Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q>' a" and A\<^sub>1\<^sub>0: "\<forall>a. \<Y> (\<Q>' a) (\<Q> a)" using A\<^sub>1 by (blast dest: weak_basic_sim_opening_elim)
    then obtain \<P>' where A\<^sub>1\<^sub>1: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>' a" and A\<^sub>1\<^sub>2: "\<forall>a. \<X> (\<P>' a) (\<Q>' a)"
      using A\<^sub>3 and A\<^sub>4 and A\<^sub>9 using weak_basic_sim_opening_elim2 by blast
    moreover have "\<forall>a. \<Z> (\<P>' a) (\<Q> a)" using A\<^sub>1\<^sub>2 and A\<^sub>1\<^sub>0 and `\<X> OO \<Y> \<le> \<Z>` by blast
    ultimately show ?case by blast
  qed
qed

(* TODO: Prove it. *)
lemma pre_weak_basic_receive_preservation: "(\<And>x. \<X> (\<P> x) (\<Q> x)) \<Longrightarrow> c \<triangleright>\<degree> x. \<P> x \<leadsto>\<^sub>\<flat><\<X>> c \<triangleright>\<degree> x. \<Q> x" sorry

(* TODO: Prove it. *)
lemma pre_left_weak_basic_parallel_preservation:
  assumes "P \<leadsto>\<^sub>\<flat><\<X>> Q"
  and     "\<X> P Q"
  and     "\<And>S T U. \<X> S T \<Longrightarrow> \<Y> (U \<parallel> S) (U \<parallel> T)"
  and     "\<And>\<S> \<T>. (\<And>x. \<Y> (\<S> x) (\<T> x)) \<Longrightarrow> \<Y> (\<nu>\<degree> x. \<S> x) (\<nu>\<degree> x. \<T> x)"
  shows   "R \<parallel> P \<leadsto>\<^sub>\<flat><\<Y>> R \<parallel> Q"
  sorry

(* TODO: Prove it. *)
lemma pre_weak_basic_new_channel_preservation:
  assumes "\<And>x. \<P> x \<leadsto>\<^sub>\<flat><\<X>> \<Q> x"
  and     "\<And>\<R> \<S> y. (\<And>x. \<X> (\<R> x) (\<S> x)) \<Longrightarrow> \<Y> (\<nu>\<degree> y. \<R> y) (\<nu>\<degree> y. \<S> y)"
  and     "\<X> \<le> \<Y>"
  shows   "\<nu>\<degree> x. \<P> x \<leadsto>\<^sub>\<flat><\<Y>> \<nu>\<degree> x. \<Q> x"
  sorry

(** Weak basic bisimulation **)

lemma weak_basic_sim_monotonicity_aux [mono]: "\<X> \<le> \<Y> \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> Q \<longrightarrow> P \<leadsto>\<^sub>\<flat><\<Y>> Q"
  by (auto intro: weak_basic_sim_monotonicity)

coinductive
  weak_basic_bisimilarity :: "process \<Rightarrow> process \<Rightarrow> bool" (infixr "\<approx>\<^sub>\<flat>" 50)
where
  step: "\<lbrakk> P \<leadsto>\<^sub>\<flat><op \<approx>\<^sub>\<flat>> Q; Q \<approx>\<^sub>\<flat> P \<rbrakk> \<Longrightarrow> P \<approx>\<^sub>\<flat> Q"

(*** Primitive inference rules (coinduction, introduction and elimination) ***)

(**** Up-to techniques for the bisimilarity proof method. ****)

(* Bisimulation up-to \<union>. *)

lemma weak_basic_bisim_up_to_union_aux[consumes 1, case_names weak_basic_bisim, case_conclusion weak_basic_bisim step]:
  assumes related: "\<X> P Q"
  and     step:    "\<And>P Q. \<X> P Q \<Longrightarrow> P \<leadsto>\<^sub>\<flat><(\<X> \<squnion> op \<approx>\<^sub>\<flat>)> Q \<and> (\<X> \<squnion> op \<approx>\<^sub>\<flat>) Q P"
  shows            "P \<approx>\<^sub>\<flat> Q"
proof -
  have aux: "\<X> \<squnion> op \<approx>\<^sub>\<flat> = (\<lambda>P Q. \<X> P Q \<or> P \<approx>\<^sub>\<flat> Q)" by blast
  show ?thesis using related
    by (coinduct, force dest: step simp add: aux)
qed

lemma weak_basic_bisim_up_to_union[consumes 1, case_names sim sym]:
  assumes "\<X> P Q"
  and     "\<And>R S. \<X> R S \<Longrightarrow> R \<leadsto>\<^sub>\<flat><(\<X> \<squnion> op \<approx>\<^sub>\<flat>)> S"
  and     "\<And>R S. \<X> R S \<Longrightarrow> \<X> S R"
  shows   "P \<approx>\<^sub>\<flat> Q"
  using assms
by (coinduct rule: weak_basic_bisim_up_to_union_aux) auto

(**** Basic bisimilarity proof method. *****)

lemma weak_basic_bisim_proof_method_aux[consumes 1, case_names weak_basic_bisim, case_conclusion weak_basic_bisim step]:
  assumes related: "\<X> P Q"
  and     step:    "\<And>P Q. \<X> P Q \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> Q \<and> \<X> Q P"
  shows            "P \<approx>\<^sub>\<flat> Q"
  using related
proof (coinduct rule: weak_basic_bisim_up_to_union_aux)
  case (weak_basic_bisim P Q)
  from step[OF this] show ?case using weak_basic_sim_monotonicity by blast
qed

lemma weak_basic_bisim_proof_method[consumes 1, case_names sim sym]:
  assumes "\<X> P Q"
  and     "\<And>P Q. \<X> P Q \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> Q"
  and     "\<And>P Q. \<X> P Q \<Longrightarrow> \<X> Q P"
  shows   "P \<approx>\<^sub>\<flat> Q"
  using assms
by (coinduct rule: weak_basic_bisim_proof_method_aux) auto

(**** Elimination rules. *****)

lemma weak_basic_bisim_elim1: "P \<approx>\<^sub>\<flat> Q \<Longrightarrow> P \<leadsto>\<^sub>\<flat><op \<approx>\<^sub>\<flat>> Q"
  by (auto dest: weak_basic_bisimilarity.cases)

lemma weak_basic_bisim_elim2: "P \<approx>\<^sub>\<flat> Q \<Longrightarrow> Q \<approx>\<^sub>\<flat> P"
  by (auto dest: weak_basic_bisimilarity.cases)

(**** Introduction rule. *****)

lemma weak_basic_bisim_intro: "\<lbrakk> P \<leadsto>\<^sub>\<flat><op \<approx>\<^sub>\<flat>> Q; Q \<approx>\<^sub>\<flat> P \<rbrakk> \<Longrightarrow> P \<approx>\<^sub>\<flat> Q"
  by (auto intro: weak_basic_bisimilarity.intros)

(*** Weak bisimilarity includes strong bisimilarity ***)

(* TODO: Prove it. *)
lemma strong_basic_sim_imp_weak_basic_sim: "P \<preceq>\<^sub>\<flat> Q \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> Q"
  sorry

(* TODO: Prove it. *)
lemma strong_basic_bisim_imp_weak_basic_bisim: "P \<sim>\<^sub>\<flat> Q \<Longrightarrow> P \<approx>\<^sub>\<flat> Q"
  sorry

(*** Weak bisimilarity is an equivalence relation ***)

lemma weak_basic_bisim_reflexivity: "P \<approx>\<^sub>\<flat> P"
proof -
  have "P = P" by simp
  then show ?thesis
    using weak_basic_bisim_proof_method and weak_basic_sim_reflexivity by blast
qed

lemma weak_basic_bisim_symmetry [sym]: "P \<approx>\<^sub>\<flat> Q \<Longrightarrow> Q \<approx>\<^sub>\<flat> P"
  using weak_basic_bisim_elim2 by auto

lemma weak_basic_bisim_transitivity [trans]: "\<lbrakk> P \<approx>\<^sub>\<flat> Q; Q \<approx>\<^sub>\<flat> R \<rbrakk> \<Longrightarrow> P \<approx>\<^sub>\<flat> R"
proof -
  assume "P \<approx>\<^sub>\<flat> Q" and "Q \<approx>\<^sub>\<flat> R"
  let ?\<X> = "op \<approx>\<^sub>\<flat> OO op \<approx>\<^sub>\<flat>"
  have "?\<X> P R" using \<open>P \<approx>\<^sub>\<flat> Q\<close> and \<open>Q \<approx>\<^sub>\<flat> R\<close> by blast
  then show ?thesis
  proof (coinduct rule: weak_basic_bisim_proof_method)
    case (sim P R)
    then obtain Q where "P \<approx>\<^sub>\<flat> Q" and "Q \<approx>\<^sub>\<flat> R" using \<open>?\<X> P R\<close> by auto
    then have "Q \<leadsto>\<^sub>\<flat><op \<approx>\<^sub>\<flat>> R" using weak_basic_bisim_elim1 by auto
    moreover have "?\<X> \<le> ?\<X>" by simp
    ultimately show ?case using weak_basic_bisim_elim1 and weak_basic_sim_transitivity and \<open>P \<approx>\<^sub>\<flat> Q\<close> by blast
  next
    case (sym P R)
    then show ?case using weak_basic_bisim_symmetry by auto
  qed
qed

(*** Preservation laws ***)
(* TODO: Prove them. *)

lemma weak_basic_receive_preservation: "(\<And>x. \<P> x \<approx>\<^sub>\<flat> \<Q> x) \<Longrightarrow> m \<triangleright> x. \<P> x \<approx>\<^sub>\<flat> m \<triangleright> x. \<Q> x" sorry
lemma weak_basic_parallel_preservation: "P \<approx>\<^sub>\<flat> Q \<Longrightarrow> P \<parallel> R \<approx>\<^sub>\<flat> Q \<parallel> R" sorry
lemma weak_basic_new_channel_preservation: "(\<And>a. \<P> a \<approx>\<^sub>\<flat> \<Q> a) \<Longrightarrow> \<nu> a. \<P> a \<approx>\<^sub>\<flat> \<nu> a. \<Q> a" sorry

(*** Structural congruence laws ***)

lemma weak_basic_parallel_scope_extension: "\<nu> a. \<P> a \<parallel> Q \<approx>\<^sub>\<flat> \<nu> a. (\<P> a \<parallel> Q)"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_parallel_scope_extension by simp

lemma weak_basic_new_channel_scope_extension: "\<nu> b. \<nu> a. \<P> a b \<approx>\<^sub>\<flat> \<nu> a. \<nu> b. \<P> a b"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_new_channel_scope_extension by simp

lemma weak_basic_parallel_unit: "\<zero> \<parallel> P \<approx>\<^sub>\<flat> P"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_parallel_unit by simp

lemma weak_basic_parallel_associativity: "(P \<parallel> Q) \<parallel> R \<approx>\<^sub>\<flat> P \<parallel> (Q \<parallel> R)"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_parallel_associativity by simp

lemma weak_basic_parallel_commutativity: "P \<parallel> Q \<approx>\<^sub>\<flat> Q \<parallel> P"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_parallel_commutativity by simp

end
