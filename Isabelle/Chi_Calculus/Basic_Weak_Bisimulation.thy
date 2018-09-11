theory Basic_Weak_Bisimulation
  imports Basic_Transition_System
begin

(* Sequence of \<tau>-transitions: \<Longrightarrow>\<^sub>\<flat> *)

abbreviation tau_sequence :: "
    ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
  ("_ \<turnstile> _ \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> _" [51, 0, 51] 50)
where
  "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<equiv> (P, Q) \<in> {(P, Q) | P Q. \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q}^*"

lemma tau_sequence_refl: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P"
  by simp

lemma tau_sequence_non_empty: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q; P \<noteq> Q \<rbrakk> \<Longrightarrow> \<exists>R. \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R \<and> \<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (smt Pair_inject converse_rtranclE mem_Collect_eq)

lemma tau_sequence_trans: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by simp

lemma tau_transition_is_tau_sequence: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by auto

lemma append_tau_transition_to_tau_sequence_is_tau_sequence:  "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (metis (mono_tags, lifting) mem_Collect_eq rtrancl.simps)

lemma prepend_tau_transition_to_tau_sequence_is_tau_sequence: "\<lbrakk> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (simp add: rtrancl_into_trancl2 trancl_into_rtrancl)

lemma tau_sequence_induction[consumes 1, case_names tau_seq_refl tau_seq_step]:
  assumes "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  and     "\<PP> P"
  and     "\<And>R S. \<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S; \<PP> R \<rbrakk> \<Longrightarrow> \<PP> S"
  shows   "\<PP> Q"
  using assms
  by (induction rule: rtrancl_induct) auto

(* The lifted operational semantics rules for \<tau>-sequences. *)
(* \<tau>-sequence relation behaves as expected w.r.t. process operators (except, of course, \<triangleright> and \<triangleleft>) *)

lemma tau_sequence_parallel_preservation_left: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R P')
  then have "\<Gamma> \<turnstile> R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q"
    using tau_seq_step.hyps(2) by (simp add: acting_left)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_parallel_preservation_right: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> Q'"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R Q')
  then have "\<Gamma> \<turnstile> P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P \<parallel> Q'"
    using tau_seq_step.hyps(2) by (simp add: acting_right)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_parallel_preservation: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'; \<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'" and "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
  have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
    using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> and tau_sequence_parallel_preservation_left by simp
  moreover have "\<Gamma> \<turnstile> P' \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'"
    using \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> and tau_sequence_parallel_preservation_right by simp
  finally show ?thesis
    by simp
qed

lemma tau_sequence_new_channel_preservation: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<Longrightarrow> \<Gamma> \<turnstile> \<nu> a. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<nu> a. Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R P')
  then have "\<Gamma> \<turnstile> \<nu> a. R  \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. P'"
    using tau_seq_step(2) by (simp add: acting_scope)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_invocation_preservation: "\<lbrakk> \<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q; \<Gamma> N V \<noteq> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
proof -
  assume "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" and "\<Gamma> N V \<noteq> Q"
  then obtain R where Tran: "\<Gamma> \<turnstile> \<Gamma> N V \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R" and Seq: "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
    using tau_sequence_non_empty by blast
  then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R"
    using Tran and invocation by fastforce
  then show ?thesis
   using Seq and prepend_tau_transition_to_tau_sequence_is_tau_sequence by simp
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
  weak_tau_respecting_basic_transition :: "
    ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) basic_residual \<Rightarrow>
    bool"
  ("_ \<turnstile> _ \<Longrightarrow>\<^sub>\<flat>_" [51, 0, 51] 50)
  where
   "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>C \<equiv>
      case C of
        \<lbrace>\<alpha>\<rbrace> Q     \<Rightarrow> \<exists>R S. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<and> \<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q |
        Opening \<Q> \<Rightarrow> \<exists>R \<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a)"

lemma weak_tau_respecting_basic_transition_acting_intro: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S; \<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  using weak_tau_respecting_basic_transition_def by force

lemma weak_tau_respecting_basic_transition_opening_intro: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a; \<And>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  using weak_tau_respecting_basic_transition_def by force

lemma weak_tau_respecting_basic_transition_acting_elim: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<exists>R S. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<and> \<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (simp split: basic_residual.split add: weak_tau_respecting_basic_transition_def)

lemma weak_tau_respecting_basic_transition_opening_elim: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<exists>R \<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a)"
  by (simp split: basic_residual.split add: weak_tau_respecting_basic_transition_def)

lemma weak_tau_respecting_basic_transition_single_acting: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  using weak_tau_respecting_basic_transition_acting_intro by blast

lemma weak_tau_respecting_basic_transition_single_opening: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  using weak_tau_respecting_basic_transition_opening_intro by blast

lemma weak_tau_respecting_basic_transition_tau: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q"
  then obtain R and S where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" using \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S\<close> and tau_transition_is_tau_sequence by simp
  then show ?thesis using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> by (simp add: tau_sequence_trans)
qed

lemma prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  then obtain S and T where "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" and "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T" and "\<Gamma> \<turnstile> T \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<close> and \<open>\<Gamma> \<turnstile> T \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma prepend_tau_sequence_to_weak_tau_respecting_basic_transition_opening: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then obtain S and \<P> where "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" and "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" and "\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a" using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a\<close> and \<open>\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a\<close> by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

lemma append_tau_sequence_to_weak_tau_respecting_basic_transition_acting: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R" and "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  then obtain S and T where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" and "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T" and "\<Gamma> \<turnstile> T \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "\<Gamma> \<turnstile> T \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" using \<open>\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<close> and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma append_tau_sequence_to_weak_tau_respecting_basic_transition_opening: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a; \<And>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" and "\<And>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a"
  then obtain S and \<S> where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S" and "\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<S> a" and "\<forall>a. \<Gamma> \<turnstile> \<S> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a" using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "\<And>a. \<Gamma> \<turnstile> \<S> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a" using \<open>\<And>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a\<close> and \<open>\<forall>a. \<Gamma> \<turnstile> \<S> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> using tau_sequence_trans by fastforce
  then show ?thesis using \<open>\<Gamma> \<turnstile> S \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<S> a\<close> and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> S\<close> using weak_tau_respecting_basic_transition_opening_intro by fastforce
qed

(** Lifted weak \<tau>-respecting basic operational semantics **)

lemma weak_tau_respecting_basic_transition_sending: "\<Gamma> \<turnstile> m \<triangleleft> V \<Longrightarrow>\<^sub>\<flat>\<lbrace>m \<triangleleft> V\<rbrace> send_cont m V"
  using weak_tau_respecting_basic_transition_def and sending by force

lemma weak_tau_respecting_basic_transition_receiving: "\<Gamma> \<turnstile> m \<triangleright> x. \<P> x \<Longrightarrow>\<^sub>\<flat>\<lbrace>m \<triangleright> V\<rbrace> \<P> V"
  using weak_tau_respecting_basic_transition_def and receiving by force

lemma weak_tau_respecting_basic_transition_communication: "\<lbrakk> \<eta> \<bowtie> \<mu>; \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'; \<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'"
proof -
  assume "\<eta> \<bowtie> \<mu>" and "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'" and "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'"
  then obtain R and S where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'"
    using weak_tau_respecting_basic_transition_acting_elim and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'\<close> by fastforce
  moreover obtain T and U where "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> T" and "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> U" and "\<Gamma> \<turnstile> U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
    using weak_tau_respecting_basic_transition_acting_elim and \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'\<close> by fastforce
  ultimately show ?thesis
  proof -
    have "\<Gamma> \<turnstile> R \<parallel> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S \<parallel> U"
      using \<open>\<eta> \<bowtie> \<mu>\<close> and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> S\<close> and \<open>\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> U\<close> using communication by fastforce
    moreover have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> T"
      using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> T\<close> and tau_sequence_parallel_preservation by simp
    moreover have "\<Gamma> \<turnstile> S \<parallel> U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'"
      using \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> and \<open>\<Gamma> \<turnstile> U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> and tau_sequence_parallel_preservation by simp
    ultimately show "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'"
      using weak_tau_respecting_basic_transition_acting_intro by simp
  qed
qed

lemma weak_tau_respecting_basic_transition_opening: "\<Gamma> \<turnstile> \<nu> a. \<P> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  by (simp add: opening weak_tau_respecting_basic_transition_single_opening)

lemma weak_tau_respecting_basic_transition_invocation: "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C \<Longrightarrow> \<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sub>\<flat>C"
proof (cases C)
  assume "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C"
  case (Acting \<alpha> P)
  then obtain R and S where "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P"
    using weak_tau_respecting_basic_transition_acting_elim and \<open>\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C\<close> by fastforce
  then show ?thesis
  proof (cases "\<Gamma> N V = R")
    case True
    then have "\<Gamma> \<turnstile> \<Gamma> N V \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S"
      using \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> by simp
    then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S"
      by (simp add: invocation)
    moreover have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<langle>N\<rangle> V"
      by (simp add: tau_sequence_refl)
    ultimately show ?thesis
      using Acting and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<close> and weak_tau_respecting_basic_transition_acting_intro by blast
  next
    case False
    then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R"
      using \<open>\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and tau_sequence_invocation_preservation by simp
    then show ?thesis
      using Acting and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<close> and weak_tau_respecting_basic_transition_acting_intro
      by blast
  qed
next
  assume "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C"
  case (Opening \<P>)
  then obtain R and \<Q> where "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" and "\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a"
    using weak_tau_respecting_basic_transition_opening_elim and \<open>\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C\<close> by fastforce
  then show ?thesis
  proof (cases "\<Gamma> N V = R")
    case True
      then have "\<Gamma> \<turnstile> \<Gamma> N V \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
        using \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close> by simp
      then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
        by (simp add: invocation)
      moreover have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<langle>N\<rangle> V"
        by (simp add: tau_sequence_refl)
      ultimately show ?thesis
        using Opening and \<open>\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> and weak_tau_respecting_basic_transition_opening_intro by blast
  next
    case False
      then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R"
        using \<open>\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and tau_sequence_invocation_preservation by simp
      then show ?thesis
        using Opening and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close> and \<open>\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> and weak_tau_respecting_basic_transition_opening_intro
        by blast
  qed
qed

lemma weak_tau_respecting_basic_transition_acting_left: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P' \<parallel> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P'"
  then obtain R and S where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> Q"
    using tau_sequence_parallel_preservation and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<parallel> Q"
    using acting_left and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> S \<parallel> Q  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
    using tau_sequence_parallel_preservation_left and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> by simp
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma weak_tau_respecting_basic_transition_acting_right: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P \<parallel> Q'"
proof -
  assume "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'"
  then obtain R and S where "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> R"
    using tau_sequence_parallel_preservation and \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P \<parallel> S"
    using acting_right and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> P \<parallel> S  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> Q'"
    using tau_sequence_parallel_preservation_right and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> by simp
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma weak_tau_respecting_basic_transition_opening_left: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<parallel> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  then obtain R and \<Q> where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" and "\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a"
    using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> Q"
    using tau_sequence_parallel_preservation and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<parallel> Q"
    using opening_left and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close> by fastforce
  moreover have "\<And>a. \<Gamma> \<turnstile> \<Q> a \<parallel> Q  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a \<parallel> Q"
    using tau_sequence_parallel_preservation_left and \<open>\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> by fastforce
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

lemma weak_basic_transition_opening_right: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P \<parallel> \<Q> a"
proof -
  assume "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then obtain R and \<P> where "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" and "\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a"
    using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> R"
    using tau_sequence_parallel_preservation and \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P \<parallel> \<P> a"
    using opening_right and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a\<close> by fastforce
  moreover have "\<And>a. \<Gamma> \<turnstile> P \<parallel> \<P> a  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> \<Q> a"
    using tau_sequence_parallel_preservation_right and \<open>\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a\<close> by fastforce
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

(* TODO: Prove. *)
lemma weak_tau_respecting_basic_transition_scoped_acting: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<R> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<R> a"
  sorry

(* TODO: Prove. *)
lemma weak_tau_respecting_basic_transition_scoped_opening: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<R> a b \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<R> a b"
  sorry

(** Weak basic transition \<Longrightarrow>\<^sub>\<flat>\<^sup>^ **)

definition weak_basic_transition :: "
  ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
  ('name, 'chan, 'val) process \<Rightarrow>
  ('name, 'chan, 'val) basic_residual \<Rightarrow>
  bool"
  ("_ \<turnstile> _ \<Longrightarrow>\<^sub>\<flat>\<^sup>^_" [51, 0, 51] 50)
  where
   "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^C \<equiv>
      case C of
        \<lbrace>\<alpha>\<rbrace> Q \<Rightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<or> (\<alpha> = \<tau> \<and> P = Q) |
        Opening \<Q> \<Rightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> Opening \<Q>"

lemma prepend_tau_transition_to_weak_basic_transition: "\<lbrakk> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R" and "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  then have "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<or> \<alpha> = \<tau> \<and> R = Q"
    by (simp add: weak_basic_transition_def)
  then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<or> \<alpha> = \<tau> \<and> P = Q"
    using \<open>\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R\<close> and prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting and weak_tau_respecting_basic_transition_single_acting by blast
  then show ?thesis
    by (simp add: weak_basic_transition_def)
qed

lemma append_tau_transition_to_weak_basic_transition: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q" and "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R"
  then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R \<or> \<alpha> = \<tau> \<and> P = R"
    by (simp add: weak_basic_transition_def)
  then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<or> \<alpha> = \<tau> \<and> P = Q"
    using \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q\<close> and append_tau_sequence_to_weak_tau_respecting_basic_transition_acting and weak_tau_respecting_basic_transition_single_acting by blast
  then show ?thesis
    by (simp add: weak_basic_transition_def)
qed

lemma tau_sequence_is_weak_basic_tau_transition: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by (simp add: weak_basic_transition_def)
next
  case (tau_seq_step R S)
  then show ?case by (simp add: append_tau_transition_to_weak_basic_transition)
qed

lemma weak_basic_tau_transition_is_tau_sequence: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> Q"
  then show ?thesis
  proof (cases "P = Q")
    case True
    then show ?thesis by (simp add: tau_sequence_refl)
  next
    case False
    then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q" using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> Q\<close> and weak_basic_transition_def by force
    then show ?thesis using weak_tau_respecting_basic_transition_tau by fastforce
  qed
qed

lemma weak_basic_transition_refl_intro: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> P"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_step_intro: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_step_elim: "\<lbrakk> P \<noteq> Q; \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_induction
  [consumes 1, case_names weak_basic_tran_refl weak_basic_tran_step]:
  assumes "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  and     "\<PP> \<tau> P"
  and     "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<PP> \<alpha> Q"
  shows   "\<PP> \<alpha> Q"
  using assms
  by (auto simp add: weak_basic_transition_def)

lemma weak_basic_transition_single_acting: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  using weak_tau_respecting_basic_transition_acting_intro and weak_basic_transition_step_intro by fastforce

lemma prepend_tau_sequence_to_weak_basic_transition: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
  then show ?thesis
  proof (cases "R = Q")
    case True
    then have A1: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and True by simp
    moreover have A2: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q" using \<open>\<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<alpha> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_basic_tau_transition)
    next
      case False
      then have "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using A2 and False by (simp add: weak_basic_transition_def)
      then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using A1 by (simp add: prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting)
      then show ?thesis by (simp add: weak_basic_transition_step_intro)
    qed
  next
    case False
    then have "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using \<open>\<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q\<close> by (simp add: weak_basic_transition_step_elim)
    then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting by simp
    then show ?thesis by (simp add: weak_basic_transition_step_intro)
  qed
qed

lemma append_tau_sequence_to_weak_basic_transition: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R" and "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  then show ?thesis
  proof (cases "P = R")
    case True
    then have A1: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" using \<open>\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> and True by simp
    moreover have A2: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P" using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<alpha> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_basic_tau_transition)
    next
      case False
      then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P" using A2 and False by (simp add: weak_basic_transition_def)
      then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using A1 by (simp add: append_tau_sequence_to_weak_tau_respecting_basic_transition_acting)
      then show ?thesis by (simp add: weak_basic_transition_step_intro)
    qed
  next
    case False
    then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R" using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> R\<close> by (simp add: weak_basic_transition_step_elim)
    then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q" using \<open>\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<close> and append_tau_sequence_to_weak_tau_respecting_basic_transition_acting by simp
    then show ?thesis by (simp add: weak_basic_transition_step_intro)
  qed
qed

(** Lifted weak basic operational semantics **)

lemma weak_basic_transition_sending: "\<Gamma> \<turnstile> m \<triangleleft> V \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>m \<triangleleft> V\<rbrace> send_cont m V"
  by (simp add: weak_tau_respecting_basic_transition_sending weak_basic_transition_def)

lemma weak_basic_transition_receiving: "\<Gamma> \<turnstile> m \<triangleright> x. \<P> x \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>m \<triangleright> V\<rbrace> \<P> V"
  by (simp add: weak_tau_respecting_basic_transition_receiving weak_basic_transition_def)

lemma weak_basic_transition_communication: "\<lbrakk> \<eta> \<bowtie> \<mu>; \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>IO \<eta>\<rbrace> P'; \<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>IO \<mu>\<rbrace> Q' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'"
  by (simp add: weak_tau_respecting_basic_transition_communication weak_basic_transition_def)

lemma weak_basic_transition_acting_left: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<parallel> Q"
  by (auto simp add: weak_tau_respecting_basic_transition_acting_left weak_basic_transition_def)

lemma weak_basic_transition_acting_right: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P \<parallel> Q'"
  by (auto simp add: weak_tau_respecting_basic_transition_acting_right weak_basic_transition_def)

(* Weak basic bisimilarity *)

(** Weak basic simulation **)

definition weak_basic_simulation :: "
  ('name, 'chan, 'val) process \<Rightarrow>
  (('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> bool) \<Rightarrow>
  ('name, 'chan, 'val) process \<Rightarrow>
  bool"
  ("_ \<leadsto>\<^sub>\<flat><_> _" [80, 80, 80] 80)
  where
    "P \<leadsto>\<^sub>\<flat><\<X>> Q \<equiv>
      (\<forall>\<Gamma> \<alpha> Q'. \<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<longrightarrow> (\<exists>P'. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'))
      \<and>
      (\<forall>\<Gamma> \<Q>. \<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<longrightarrow> (\<exists>\<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<X> (\<P> a) (\<Q> a))))"

lemma weak_basic_sim_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> Q \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<Y>> Q"
  by (simp add: weak_basic_simulation_def) blast

lemma weak_basic_sim_cases
  [case_names acting opening]:
  assumes acting:  "\<And>\<Gamma> \<alpha> Q'. \<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<Longrightarrow> \<exists>P'. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'"
  and     opening: "\<And>\<Gamma> \<Q>. \<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<exists>\<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<X> (\<P> a) (\<Q> a))"
  shows            "P \<leadsto>\<^sub>\<flat><\<X>> Q"
  using assms
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_acting_elim: "\<lbrakk> P \<leadsto>\<^sub>\<flat><\<X>> Q; \<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<rbrakk> \<Longrightarrow> \<exists>P'. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'"
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_opening_elim: "\<lbrakk> P \<leadsto>\<^sub>\<flat><\<X>> Q; \<Gamma> \<turnstile> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<rbrakk> \<Longrightarrow> \<exists>\<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<X> (\<P> a) (\<Q> a))"
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_reflexivity: "(\<And>P. \<X> P P) \<Longrightarrow> P \<leadsto>\<^sub>\<flat><\<X>> P"
  using weak_basic_simulation_def weak_basic_transition_single_acting weak_tau_respecting_basic_transition_single_opening by blast

lemma weak_basic_sim_tau_sequence:
  assumes A\<^sub>1: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
  and     A\<^sub>2: "\<X> P Q"
  and     A\<^sub>3: "\<And>R S. \<X> R S \<Longrightarrow> R \<leadsto>\<^sub>\<flat><\<X>> S"
  shows       "\<exists>P'. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<and> \<X> P' Q'"
  using assms
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  moreover have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P" by simp
  ultimately show ?case using A\<^sub>3 and A\<^sub>2 by blast
next
  case (tau_seq_step Q' Q'')
  have "\<exists>P'. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<and> \<X> P' Q'" using tau_seq_step.prems and tau_seq_step.IH by simp
  then obtain P' where A\<^sub>4: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'" and A\<^sub>5: "\<X> P' Q'" by auto
  then have "P' \<leadsto>\<^sub>\<flat><\<X>> Q'" using A\<^sub>5 and A\<^sub>3 by simp
  moreover have A\<^sub>6: "\<Gamma> \<turnstile> Q' \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q''" by fact
  ultimately obtain P'' where A\<^sub>7: "\<Gamma> \<turnstile> P' \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> P''" and A\<^sub>8: "\<X> P'' Q''" by (blast dest: weak_basic_sim_acting_elim)
  then have "\<Gamma> \<turnstile> P' \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P''" using A\<^sub>7 and weak_basic_tau_transition_is_tau_sequence by blast
  then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P''" using A\<^sub>4 by simp
  then show ?case using A\<^sub>8 by auto
qed

(* TODO: Prove it. *)
lemma weak_basic_sim_tau_sequence2:
  assumes A\<^sub>1: "\<And>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q>' a"
  and     A\<^sub>2: "\<And>a. \<X> (\<P> a) (\<Q> a)"
  and     A\<^sub>3: "\<And>R S. \<X> R S \<Longrightarrow> R \<leadsto>\<^sub>\<flat><\<X>> S"
  shows       "\<exists>\<P>'. \<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P>' a \<and> \<X> (\<P>' a) (\<Q>' a)"
  sorry

lemma weak_basic_sim_acting_elim2:
  assumes A\<^sub>1: "\<And>R S. \<X> R S \<Longrightarrow> R \<leadsto>\<^sub>\<flat><\<X>> S"
  and     A\<^sub>2: "\<X> P Q"
  and     A\<^sub>3: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q'"
  shows       "\<exists>P'. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'"
  using assms
proof -
  assume "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q'"
  then show "\<exists>P'. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q'"
  proof (induction rule: weak_basic_transition_induction)
    case weak_basic_tran_refl
    then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> P" by (simp add: weak_basic_transition_refl_intro)
    then show ?case using A\<^sub>2 by auto
  next
    case weak_basic_tran_step
    have "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'" by fact
    then obtain Q\<^sub>2 and Q\<^sub>3 where A\<^sub>4: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<^sub>2" and A\<^sub>5: "\<Gamma> \<turnstile> Q\<^sub>2 \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q\<^sub>3" and A\<^sub>6: "\<Gamma> \<turnstile> Q\<^sub>3 \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
      by (blast dest: weak_tau_respecting_basic_transition_acting_elim)
    then have "\<exists>P\<^sub>2. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<^sub>2 \<and> \<X> P\<^sub>2 Q\<^sub>2" using A\<^sub>4 and A\<^sub>2 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
    then obtain P\<^sub>2 where A\<^sub>7: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<^sub>2" and A\<^sub>8: "\<X> P\<^sub>2 Q\<^sub>2" by auto
    then have "P\<^sub>2 \<leadsto>\<^sub>\<flat><\<X>> Q\<^sub>2" using A\<^sub>8 and A\<^sub>1 by simp
    then obtain P\<^sub>3 where A\<^sub>9: "\<Gamma> \<turnstile> P\<^sub>2 \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P\<^sub>3" and A\<^sub>1\<^sub>0: "\<X> P\<^sub>3 Q\<^sub>3" using A\<^sub>5 by (blast dest: weak_basic_sim_acting_elim)
    then have "\<exists>P'. \<Gamma> \<turnstile> P\<^sub>3 \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<and> \<X> P' Q'" using A\<^sub>6 and A\<^sub>1\<^sub>0 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
    then obtain P' where A\<^sub>1\<^sub>1: "\<Gamma> \<turnstile> P\<^sub>3 \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'" and A\<^sub>1\<^sub>2: "\<X> P' Q'" by auto
    then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P'" using A\<^sub>7 and A\<^sub>9 and A\<^sub>1\<^sub>1
      by (blast dest: prepend_tau_sequence_to_weak_basic_transition append_tau_sequence_to_weak_basic_transition)
    then show ?case using A\<^sub>1\<^sub>2 by auto
  qed
qed

lemma weak_basic_sim_opening_elim2:
  assumes A\<^sub>1: "\<And>R S. \<X> R S \<Longrightarrow> R \<leadsto>\<^sub>\<flat><\<X>> S"
  and     A\<^sub>2: "\<X> P Q"
  and     A\<^sub>3: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  shows       "\<exists>\<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<X> (\<P> a) (\<Q> a))"
  using assms
proof -
  assume "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then obtain Q\<^sub>2 and \<Q>\<^sub>3 where A\<^sub>4: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q\<^sub>2" and A\<^sub>5: "\<Gamma> \<turnstile> Q\<^sub>2 \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q>\<^sub>3 a" and A\<^sub>6: "\<forall>a. \<Gamma> \<turnstile> \<Q>\<^sub>3 a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a"
    by (blast dest: weak_tau_respecting_basic_transition_opening_elim)
  then have "\<exists>P\<^sub>2. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<^sub>2 \<and> \<X> P\<^sub>2 Q\<^sub>2" using A\<^sub>4 and A\<^sub>2 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
  then obtain P\<^sub>2 where A\<^sub>7: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<^sub>2" and A\<^sub>8: "\<X> P\<^sub>2 Q\<^sub>2" by auto
  then have "P\<^sub>2 \<leadsto>\<^sub>\<flat><\<X>> Q\<^sub>2" using A\<^sub>8 and A\<^sub>1 by simp
  then obtain \<P>\<^sub>3 where A\<^sub>9: "\<Gamma> \<turnstile> P\<^sub>2 \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>\<^sub>3 a" and A\<^sub>1\<^sub>0: "\<forall>a. \<X> (\<P>\<^sub>3 a) (\<Q>\<^sub>3 a)" using A\<^sub>5
    by (blast dest: weak_basic_sim_opening_elim)
  then have "\<exists>\<P>. \<forall>a. \<Gamma> \<turnstile> \<P>\<^sub>3 a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a \<and> \<X> (\<P> a) (\<Q> a)" using A\<^sub>6 and A\<^sub>1\<^sub>0 and A\<^sub>1 weak_basic_sim_tau_sequence2 by blast
  then obtain \<P> where A\<^sub>1\<^sub>1: "\<And>a. \<Gamma> \<turnstile> \<P>\<^sub>3 a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a" and A\<^sub>1\<^sub>2: "\<And>a. \<X> (\<P> a) (\<Q> a)" by auto
  then have "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" using A\<^sub>7 and A\<^sub>9 and A\<^sub>1\<^sub>1
    by (blast dest: prepend_tau_sequence_to_weak_tau_respecting_basic_transition_opening append_tau_sequence_to_weak_tau_respecting_basic_transition_opening)
  then show ?thesis using A\<^sub>1\<^sub>2 by auto
qed

lemma weak_basic_sim_transitivity:
  assumes A\<^sub>1: "Q \<leadsto>\<^sub>\<flat><\<Y>> R"
  and     A\<^sub>2: "\<X> OO \<Y> \<le> \<Z>"
  and     A\<^sub>3:"\<And>S T. \<X> S T \<Longrightarrow> S \<leadsto>\<^sub>\<flat><\<X>> T"
  and     A\<^sub>4: "\<X> P Q"
  shows "P \<leadsto>\<^sub>\<flat><\<Z>> R"
  using assms
proof -
  show ?thesis
  proof(induction rule: weak_basic_sim_cases)
    case (acting \<Gamma> \<alpha> Q')
    then have "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'" by simp
    then obtain Q\<^sub>2 where A\<^sub>5: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> Q\<^sub>2" and A\<^sub>6: "\<Y> Q\<^sub>2 Q'" using A\<^sub>1 by (blast dest: weak_basic_sim_acting_elim)
    then have "\<exists>P'. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P' \<and> \<X> P' Q\<^sub>2" using A\<^sub>3 and A\<^sub>4 and A\<^sub>5 by (blast intro: weak_basic_sim_acting_elim2)
    then obtain P' where A\<^sub>7: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> P'" and A\<^sub>8: "\<X> P' Q\<^sub>2" by auto
    then have "\<Z> P' Q'" using A\<^sub>8 and A\<^sub>6 and A\<^sub>2 by auto
    then show ?case using A\<^sub>7 by auto
  next
    case (opening \<Gamma> \<Q>)
    then have "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" by simp
    then obtain \<Q>' where "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q>' a" and "\<forall>a. \<Y> (\<Q>' a) (\<Q> a)" using `Q \<leadsto>\<^sub>\<flat><\<Y>> R` and `\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a`
      by (blast dest: weak_basic_sim_opening_elim)
    then obtain \<P>' where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P>' a" and "\<forall>a. \<X> (\<P>' a) (\<Q>' a)"
      using `\<And>S T. \<X> S T \<Longrightarrow> S \<leadsto>\<^sub>\<flat><\<X>> T` and `\<X> P Q` and `\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q>' a` using weak_basic_sim_opening_elim2 by blast
    moreover have "\<forall>a. \<Z> (\<P>' a) (\<Q> a)" using `\<forall>a. \<X> (\<P>' a) (\<Q>' a)` and `\<forall>a. \<Y> (\<Q>' a) (\<Q> a)` and `\<X> OO \<Y> \<le> \<Z>` by blast
    ultimately show ?case by blast
  qed
qed

end
