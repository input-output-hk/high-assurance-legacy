theory Basic_Weak_Bisimulation
  imports Typed_Basic_Transition_System
begin

(* Sequence of \<tau>-transitions: \<Longrightarrow>\<^sub>\<flat> *)

abbreviation tau_sequence :: "process \<Rightarrow> process \<Rightarrow> bool"
  (infix "\<Rightarrow>\<^sup>\<tau>\<^sub>\<flat>" 50)
where
  "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<equiv> (p, q) \<in> {(p, q) | p q. p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q}^*"

lemma tau_sequence_refl: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p"
  by simp

lemma tau_sequence_non_empty: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q; p \<noteq> q \<rbrakk> \<Longrightarrow> \<exists>r. p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r \<and> r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  by (smt Pair_inject converse_rtranclE mem_Collect_eq)

lemma tau_sequence_trans: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<rbrakk> \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  by simp

lemma tau_transition_is_tau_sequence: "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  by auto

lemma append_tau_transition_to_tau_sequence_is_tau_sequence:  "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<rbrakk> \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  by (metis (mono_tags, lifting) mem_Collect_eq rtrancl.simps)

lemma prepend_tau_transition_to_tau_sequence_is_tau_sequence: "\<lbrakk> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r; r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<rbrakk> \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  by (simp add: rtrancl_into_trancl2 trancl_into_rtrancl)

lemma tau_sequence_induction[consumes 1, case_names tau_seq_refl tau_seq_step]:
  assumes "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  and     "Prop p"
  and     "\<And>r s. \<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> s; Prop r \<rbrakk> \<Longrightarrow> Prop s"
  shows   "Prop q"
  using assms
  by (induction rule: rtrancl_induct) auto

(* The lifted operational semantics rules for \<tau>-sequences. *)
(* \<tau>-sequence relation behaves as expected w.r.t. process operators (except, of course, \<triangleright> and \<triangleleft>) *)

lemma tau_sequence_parallel_preservation_left: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<Longrightarrow> p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<parallel> q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step r p')
  then have "r \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> p' \<parallel> q"
    using tau_seq_step.hyps(2) by (simp add: acting_left)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_parallel_preservation_right: "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q' \<Longrightarrow> p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p \<parallel> q'"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step r q')
  then have "p \<parallel> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> p \<parallel> q'"
    using tau_seq_step.hyps(2) by (simp add: acting_right)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_parallel_preservation: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'; q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q' \<rbrakk> \<Longrightarrow> p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<parallel> q'"
proof -
  assume "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'" and "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q'"
  have "p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<parallel> q"
    using \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'\<close> and tau_sequence_parallel_preservation_left by simp
  moreover have "p' \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<parallel> q'"
    using \<open>q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q'\<close> and tau_sequence_parallel_preservation_right by simp
  finally show ?thesis
    by simp
qed

lemma tau_sequence_new_channel_preservation: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<Longrightarrow> \<nu> a. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> \<nu> a. q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step r p')
  then have "\<nu> a. r  \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. p'"
    using tau_seq_step(2) by (simp add: acting_scope)
  then show ?case
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

(* Weak Semantics *)

(** Weak \<tau>-respecting basic transition \<Longrightarrow>\<^sub>\<flat> d **)
(** NOTE: Note that even though the transition p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a appears to contain a binder into Q a, in
reality it does not. The binder occurs inside the definition, where a binds into P a. The process
P a then does a \<tau>-sequence to Q a, which "a" does not bind into, unless P a = Q a. Formally, one can
still reason about "a" as a binder: there is no way that any new names can be introduced by a \<tau>-sequence;
the name "a" can be communicated within the process, but if so it occurs free in an output-prefix in p. **)
(** TODO: Perhaps I can define a weak basic transition without using a residual, i.e. as
 weak_tau_respecting_basic_transition :: process \<Rightarrow> process \<Rightarrow> [IO action|chan] \<Rightarrow> process **)

definition
  weak_tau_respecting_basic_transition :: "process \<Rightarrow> basic_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<flat>" 50)
  where
   "p \<Longrightarrow>\<^sub>\<flat> d \<equiv>
      case d of
        \<lbrace>\<alpha>\<rbrace> q     \<Rightarrow> \<exists>r s. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r \<and> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s \<and> s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q |
        Opening Q \<Rightarrow> \<exists>r P. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r \<and> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<and> (\<forall>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a)"

lemma weak_tau_respecting_basic_transition_acting_intro: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s; s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q"
  using weak_tau_respecting_basic_transition_def by force

lemma weak_tau_respecting_basic_transition_opening_intro: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a; \<And>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
  using weak_tau_respecting_basic_transition_def by force

lemma weak_tau_respecting_basic_transition_acting_elim: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<Longrightarrow> \<exists>r s. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r \<and> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s \<and> s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  by (simp split: basic_residual.split add: weak_tau_respecting_basic_transition_def)

lemma weak_tau_respecting_basic_transition_opening_elim: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<Longrightarrow> \<exists>r P. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r \<and> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<and> (\<forall>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a)"
  by (simp split: basic_residual.split add: weak_tau_respecting_basic_transition_def)

lemma weak_tau_respecting_basic_transition_single_acting: "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q"
  using weak_tau_respecting_basic_transition_acting_intro by blast

lemma weak_tau_respecting_basic_transition_single_opening: "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
  using weak_tau_respecting_basic_transition_opening_intro by blast

lemma weak_tau_respecting_basic_transition_tau: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q"
  then obtain r and s where "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> s" and "s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s" using \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> s\<close> and tau_transition_is_tau_sequence by simp
  then show ?thesis using \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> and \<open>s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q\<close> by (simp add: tau_sequence_trans)
qed

lemma prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q"
proof -
  assume "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q"
  then obtain s and t where "r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s" and "s \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t" and "t \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q" using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s" using \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> and \<open>r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>s \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t\<close> and \<open>t \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q\<close> by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma prepend_tau_sequence_to_weak_tau_respecting_basic_transition_opening: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
proof -
  assume "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
  then obtain s and P where "r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s" and "s \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a" and "\<forall>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a" using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s" using \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> and \<open>r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>s \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close> and \<open>\<forall>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a\<close> by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

lemma append_tau_sequence_to_weak_tau_respecting_basic_transition_acting: "\<lbrakk> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> r; r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> r" and "r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  then obtain s and t where "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s" and "s \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t" and "t \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "t \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q" using \<open>r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q\<close> and \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s\<close> by (simp add: tau_sequence_trans)
  then show ?thesis using \<open>s \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t\<close> and \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s\<close> by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma append_tau_sequence_to_weak_tau_respecting_basic_transition_opening: "\<lbrakk> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a; \<And>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
proof -
  assume "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a" and "\<And>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a"
  then obtain s and S where "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s" and "s \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> S a" and "\<forall>a. S a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> P a" using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "\<And>a. S a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a" using \<open>\<And>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a\<close> and \<open>\<forall>a. S a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> P a\<close> using tau_sequence_trans by fastforce
  then show ?thesis using \<open>s \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> S a\<close> and \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> s\<close> using weak_tau_respecting_basic_transition_opening_intro by fastforce
qed

(** Lifted weak \<tau>-respecting basic operational semantics **)

lemma weak_tau_respecting_basic_transition_sending: "a \<triangleleft> x \<Longrightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<zero>"
  using weak_tau_respecting_basic_transition_def and sending by force

lemma weak_tau_respecting_basic_transition_receiving: "a \<triangleright> x. P x \<Longrightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> P x"
  using weak_tau_respecting_basic_transition_def and receiving by force

lemma weak_tau_respecting_basic_transition_communication: "\<lbrakk> \<eta> \<bowtie> \<mu>; p \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'; q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q' \<rbrakk> \<Longrightarrow> p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> p' \<parallel> q'"
proof -
  assume "\<eta> \<bowtie> \<mu>" and "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'" and "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q'"
  then obtain r and s where "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> s" and "s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'"
    using weak_tau_respecting_basic_transition_acting_elim and \<open>p \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'\<close> by fastforce
  moreover obtain t and u where "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> t" and "t \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> u" and "u \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q'"
    using weak_tau_respecting_basic_transition_acting_elim and \<open>q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q'\<close> by fastforce
  ultimately show ?thesis
  proof -
    have "r \<parallel> t \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> s \<parallel> u"
      using \<open>\<eta> \<bowtie> \<mu>\<close> and \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> s\<close> and \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> u\<close> using communication by fastforce
    moreover have "p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r \<parallel> t"
      using \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> and \<open>q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> t\<close> and tau_sequence_parallel_preservation by simp
    moreover have "s \<parallel> u \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<parallel> q'"
      using \<open>s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'\<close> and \<open>u \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q'\<close> and tau_sequence_parallel_preservation by simp
    ultimately show "p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> p' \<parallel> q'"
      using weak_tau_respecting_basic_transition_acting_intro by simp
  qed
qed

lemma weak_tau_respecting_basic_transition_opening: "\<nu> a. P a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a"
  by (simp add: opening weak_tau_respecting_basic_transition_single_opening)

lemma weak_tau_respecting_basic_transition_acting_left: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p' \<Longrightarrow> p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p' \<parallel> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p'"
  then obtain r and s where "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s" and "s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r \<parallel> q"
    using tau_sequence_parallel_preservation and \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> by fastforce
  moreover have "r \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s \<parallel> q"
    using acting_left and \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s\<close> by fastforce
  moreover have "s \<parallel> q  \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<parallel> q"
    using tau_sequence_parallel_preservation_left and \<open>s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'\<close> by simp
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma weak_tau_respecting_basic_transition_acting_right: "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q' \<Longrightarrow> p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p \<parallel> q'"
proof -
  assume "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'"
  then obtain r and s where "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s" and "s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q'"
    using weak_tau_respecting_basic_transition_acting_elim by fastforce
  then have "p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p \<parallel> r"
    using tau_sequence_parallel_preservation and \<open>q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> by fastforce
  moreover have "p \<parallel> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p \<parallel> s"
    using acting_right and \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s\<close> by fastforce
  moreover have "p \<parallel> s  \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p \<parallel> q'"
    using tau_sequence_parallel_preservation_right and \<open>s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q'\<close> by simp
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_acting_intro)
qed

lemma weak_tau_respecting_basic_transition_opening_left: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<Longrightarrow> p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<parallel> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a"
  then obtain r and Q where "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<forall>a. Q a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> P a"
    using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r \<parallel> q"
    using tau_sequence_parallel_preservation and \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> by fastforce
  moreover have "r \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<parallel> q"
    using opening_left and \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a\<close> by fastforce
  moreover have "\<And>a. Q a \<parallel> q  \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> P a \<parallel> q"
    using tau_sequence_parallel_preservation_left and \<open>\<forall>a. Q a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> P a\<close> by fastforce
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

lemma weak_basic_transition_opening_right: "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<Longrightarrow> p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> p \<parallel> Q a"
proof -
  assume "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
  then obtain r and P where "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a" and "\<forall>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a"
    using weak_tau_respecting_basic_transition_opening_elim by fastforce
  then have "p \<parallel> q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p \<parallel> r"
    using tau_sequence_parallel_preservation and \<open>q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> by fastforce
  moreover have "p \<parallel> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> p \<parallel> P a"
    using opening_right and \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close> by fastforce
  moreover have "\<And>a. p \<parallel> P a  \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p \<parallel> Q a"
    using tau_sequence_parallel_preservation_right and \<open>\<forall>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a\<close> by fastforce
  ultimately show ?thesis
    by (simp add: weak_tau_respecting_basic_transition_opening_intro)
qed

(* TODO: Prove. *)
lemma weak_tau_respecting_basic_transition_scoped_acting: "\<lbrakk> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R a \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. R a"
  sorry

(* TODO: Prove. *)
lemma weak_tau_respecting_basic_transition_scoped_opening: "\<lbrakk> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> R a b \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. R a b"
  sorry

(** Weak basic transition \<Longrightarrow>\<^sub>\<flat>\<^sup>^ **)

definition weak_basic_transition :: "process \<Rightarrow> basic_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<flat>\<^sup>^" 50)
  where
   "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^ d \<equiv>
      case d of
        \<lbrace>\<alpha>\<rbrace> q \<Rightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<or> (\<alpha> = \<tau> \<and> p = q) |
        Opening Q \<Rightarrow> p \<Longrightarrow>\<^sub>\<flat> Opening Q"

lemma prepend_tau_transition_to_weak_basic_transition: "\<lbrakk> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r; r \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
proof -
  assume "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r" and "r \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
  then have "r \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<or> \<alpha> = \<tau> \<and> r = q"
    by (simp add: weak_basic_transition_def)
  then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<or> \<alpha> = \<tau> \<and> p = q"
    using \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r\<close> and prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting and weak_tau_respecting_basic_transition_single_acting by blast
  then show ?thesis
    by (simp add: weak_basic_transition_def)
qed

lemma append_tau_transition_to_weak_basic_transition: "\<lbrakk> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> r; r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
proof -
  assume "r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q" and "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> r"
  then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> r \<or> \<alpha> = \<tau> \<and> p = r"
    by (simp add: weak_basic_transition_def)
  then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<or> \<alpha> = \<tau> \<and> p = q"
    using \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q\<close> and append_tau_sequence_to_weak_tau_respecting_basic_transition_acting and weak_tau_respecting_basic_transition_single_acting by blast
  then show ?thesis
    by (simp add: weak_basic_transition_def)
qed

lemma tau_sequence_is_weak_basic_tau_transition: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by (simp add: weak_basic_transition_def)
next
  case (tau_seq_step r s)
  then show ?case by (simp add: append_tau_transition_to_weak_basic_transition)
qed

lemma weak_basic_tau_transition_is_tau_sequence: "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> q \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> q"
  then show ?thesis
  proof (cases "p = q")
    case True
    then show ?thesis by (simp add: tau_sequence_refl)
  next
    case False
    then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q" using \<open>p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> q\<close> and weak_basic_transition_def by force
    then show ?thesis using weak_tau_respecting_basic_transition_tau by fastforce
  qed
qed

lemma weak_basic_transition_refl_intro: "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> p"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_step_intro: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_step_elim: "\<lbrakk> p \<noteq> q; p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q"
  by (simp add: weak_basic_transition_def)

lemma weak_basic_transition_induction
  [consumes 1, case_names weak_basic_tran_refl weak_basic_tran_step]:
  assumes "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
  and     "Prop \<tau> p"
  and     "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<Longrightarrow> Prop \<alpha> q"
  shows   "Prop \<alpha> q"
  using assms
  by (auto simp add: weak_basic_transition_def)

lemma weak_basic_transition_single_acting: "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
  using weak_tau_respecting_basic_transition_acting_intro and weak_basic_transition_step_intro by fastforce

lemma prepend_tau_sequence_to_weak_basic_transition: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
proof -
  assume "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r" and "r \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
  then show ?thesis
  proof (cases "r = q")
    case True
    then have A1: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q" using \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> and True by simp
    moreover have A2: "q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q" using \<open>r \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<alpha> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_basic_tau_transition)
    next
      case False
      then have "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q" using A2 and False by (simp add: weak_basic_transition_def)
      then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q" using A1 by (simp add: prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting)
      then show ?thesis by (simp add: weak_basic_transition_step_intro)
    qed
  next
    case False
    then have "r \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q" using \<open>r \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q\<close> by (simp add: weak_basic_transition_step_elim)
    then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q" using \<open>p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r\<close> and prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting by simp
    then show ?thesis by (simp add: weak_basic_transition_step_intro)
  qed
qed

lemma append_tau_sequence_to_weak_basic_transition: "\<lbrakk> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> r; r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> r" and "r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  then show ?thesis
  proof (cases "p = r")
    case True
    then have A1: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q" using \<open>r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q\<close> and True by simp
    moreover have A2: "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p" using \<open>p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> r\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<alpha> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_basic_tau_transition)
    next
      case False
      then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p" using A2 and False by (simp add: weak_basic_transition_def)
      then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q" using A1 by (simp add: append_tau_sequence_to_weak_tau_respecting_basic_transition_acting)
      then show ?thesis by (simp add: weak_basic_transition_step_intro)
    qed
  next
    case False
    then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> r" using \<open>p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> r\<close> by (simp add: weak_basic_transition_step_elim)
    then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q" using \<open>r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q\<close> and append_tau_sequence_to_weak_tau_respecting_basic_transition_acting by simp
    then show ?thesis by (simp add: weak_basic_transition_step_intro)
  qed
qed

(** Lifted weak basic operational semantics **)

lemma weak_basic_transition_sending: "a \<triangleleft> x \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>a \<triangleleft> x\<rbrace> \<zero>"
  by (simp add: weak_tau_respecting_basic_transition_sending weak_basic_transition_def)

lemma weak_basic_transition_receiving: "a \<triangleright> x. P x \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>a \<triangleright> x\<rbrace> P x"
  by (simp add: weak_tau_respecting_basic_transition_receiving weak_basic_transition_def)

lemma weak_basic_transition_communication: "\<lbrakk> \<eta> \<bowtie> \<mu>; p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>IO \<eta>\<rbrace> p'; q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>IO \<mu>\<rbrace> q' \<rbrakk> \<Longrightarrow> p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> p' \<parallel> q'"
  by (simp add: weak_tau_respecting_basic_transition_communication weak_basic_transition_def)

lemma weak_basic_transition_acting_left: "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p' \<Longrightarrow> p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p' \<parallel> q"
  by (auto simp add: weak_tau_respecting_basic_transition_acting_left weak_basic_transition_def)

lemma weak_basic_transition_acting_right: "q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q' \<Longrightarrow> p \<parallel> q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p \<parallel> q'"
  by (auto simp add: weak_tau_respecting_basic_transition_acting_right weak_basic_transition_def)

(* Weak basic bisimilarity *)

(** Weak basic simulation **)

definition weak_basic_simulation :: "process \<Rightarrow> (process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> process \<Rightarrow> bool"
  ("_ \<leadsto>\<^sub>\<flat><_> _" [50, 50, 50] 50)
  where
    "p \<leadsto>\<^sub>\<flat><\<X>> q \<equiv>
      (\<forall>\<alpha> q'. q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q' \<longrightarrow> (\<exists>p'. p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p' \<and> \<X> p' q'))
      \<and>
      (\<forall>Q. q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<longrightarrow> (\<exists>P. p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<and> (\<forall>a. \<X> (P a) (Q a))))"

abbreviation
  is_weak_basic_sim
where
  "is_weak_basic_sim \<X> \<equiv> \<forall>p q. \<X> p q \<longrightarrow> p \<leadsto>\<^sub>\<flat><\<X>> q"

lemma weak_basic_sim_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> p \<leadsto>\<^sub>\<flat><\<X>> q \<Longrightarrow> p \<leadsto>\<^sub>\<flat><\<Y>> q"
  by (simp add: weak_basic_simulation_def) blast

lemma weak_basic_sim_cases
  [case_names acting opening]:
  assumes acting:  "\<And>\<alpha> q'. q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q' \<Longrightarrow> \<exists>p'. p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p' \<and> \<X> p' q'"
  and     opening: "\<And>Q. q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<Longrightarrow> \<exists>P. p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<and> (\<forall>a. \<X> (P a) (Q a))"
  shows            "p \<leadsto>\<^sub>\<flat><\<X>> q"
  using assms
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_acting_elim: "\<lbrakk> p \<leadsto>\<^sub>\<flat><\<X>> q; q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q' \<rbrakk> \<Longrightarrow> \<exists>p'. p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p' \<and> \<X> p' q'"
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_opening_elim: "\<lbrakk> p \<leadsto>\<^sub>\<flat><\<X>> q; q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<rbrakk> \<Longrightarrow> \<exists>P. p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<and> (\<forall>a. \<X> (P a) (Q a))"
  by (simp add: weak_basic_simulation_def)

lemma weak_basic_sim_reflexivity: "(\<And>p. \<X> p p) \<Longrightarrow> p \<leadsto>\<^sub>\<flat><\<X>> p"
  using weak_basic_simulation_def weak_basic_transition_single_acting weak_tau_respecting_basic_transition_single_opening by blast

lemma weak_basic_sim_tau_sequence:
  assumes A\<^sub>1: "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q'"
  and     A\<^sub>2: "\<X> p q"
  and     A\<^sub>3: "is_weak_basic_sim \<X>"
  shows       "\<exists>p'. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<and> \<X> p' q'"
  using assms
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  moreover have "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p" by simp
  ultimately show ?case using A\<^sub>3 and A\<^sub>2 by blast
next
  case (tau_seq_step q' q'')
  have "\<exists>p'. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<and> \<X> p' q'" using tau_seq_step.prems and tau_seq_step.IH by simp
  then obtain p' where A\<^sub>4: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'" and A\<^sub>5: "\<X> p' q'" by auto
  then have "p' \<leadsto>\<^sub>\<flat><\<X>> q'" using A\<^sub>5 and A\<^sub>3 by simp
  moreover have A\<^sub>6: "q' \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q''" by fact
  ultimately obtain p'' where A\<^sub>7: "p' \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> p''" and A\<^sub>8: "\<X> p'' q''" by (blast dest: weak_basic_sim_acting_elim)
  then have "p' \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p''" using A\<^sub>7 and weak_basic_tau_transition_is_tau_sequence by blast
  then have "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p''" using A\<^sub>4 by simp
  then show ?case using A\<^sub>8 by auto
qed

(* TODO: Prove it. *)
lemma weak_basic_sim_tau_sequence2:
  assumes A\<^sub>1: "\<And>a. Q a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q' a"
  and     A\<^sub>2: "\<And>a. \<X> (P a) (Q a)"
  and     A\<^sub>3: "is_weak_basic_sim \<X>"
  shows       "\<exists>P'. \<forall>a. P a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> P' a \<and> \<X> (P' a) (Q' a)"
  sorry

lemma weak_basic_sim_acting_elim2:
  assumes A\<^sub>1: "is_weak_basic_sim \<X>"
  and     A\<^sub>2: "\<X> p q"
  and     A\<^sub>3: "q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q'"
  shows       "\<exists>p'. p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p' \<and> \<X> p' q'"
  using assms
proof -
  assume "q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q'"
  then show "\<exists>p'. p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p' \<and> \<X> p' q'"
  proof (induction rule: weak_basic_transition_induction)
    case weak_basic_tran_refl
    then have "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<tau>\<rbrace> p" by (simp add: weak_basic_transition_refl_intro)
    then show ?case using A\<^sub>2 by auto
  next
    case weak_basic_tran_step
    have "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'" by fact
    then obtain q\<^sub>2 and q\<^sub>3 where A\<^sub>4: "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q\<^sub>2" and A\<^sub>5: "q\<^sub>2 \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q\<^sub>3" and A\<^sub>6: "q\<^sub>3 \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q'"
      by (blast dest: weak_tau_respecting_basic_transition_acting_elim)
    then have "\<exists>p\<^sub>2. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p\<^sub>2 \<and> \<X> p\<^sub>2 q\<^sub>2" using A\<^sub>4 and A\<^sub>2 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
    then obtain p\<^sub>2 where A\<^sub>7: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p\<^sub>2" and A\<^sub>8: "\<X> p\<^sub>2 q\<^sub>2" by auto
    then have "p\<^sub>2 \<leadsto>\<^sub>\<flat><\<X>> q\<^sub>2" using A\<^sub>8 and A\<^sub>1 by simp
    then obtain p\<^sub>3 where A\<^sub>9: "p\<^sub>2 \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p\<^sub>3" and A\<^sub>1\<^sub>0: "\<X> p\<^sub>3 q\<^sub>3" using A\<^sub>5 by (blast dest: weak_basic_sim_acting_elim)
    then have "\<exists>p'. p\<^sub>3 \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p' \<and> \<X> p' q'" using A\<^sub>6 and A\<^sub>1\<^sub>0 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
    then obtain p' where A\<^sub>1\<^sub>1: "p\<^sub>3 \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p'" and A\<^sub>1\<^sub>2: "\<X> p' q'" by auto
    then have "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p'" using A\<^sub>7 and A\<^sub>9 and A\<^sub>1\<^sub>1
      by (blast dest: prepend_tau_sequence_to_weak_basic_transition append_tau_sequence_to_weak_basic_transition)
    then show ?case using A\<^sub>1\<^sub>2 by auto
  qed
qed

lemma weak_basic_sim_opening_elim2:
  assumes A\<^sub>1: "is_weak_basic_sim \<X>"
  and     A\<^sub>2: "\<X> p q"
  and     A\<^sub>3: "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
  shows       "\<exists>P. p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<and> (\<forall>a. \<X> (P a) (Q a))"
  using assms
proof -
  assume "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a"
  then obtain q\<^sub>2 and Q\<^sub>3 where A\<^sub>4: "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q\<^sub>2" and A\<^sub>5: "q\<^sub>2 \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q\<^sub>3 a" and A\<^sub>6: "\<forall>a. Q\<^sub>3 a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> Q a"
    by (blast dest: weak_tau_respecting_basic_transition_opening_elim)
  then have "\<exists>p\<^sub>2. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p\<^sub>2 \<and> \<X> p\<^sub>2 q\<^sub>2" using A\<^sub>4 and A\<^sub>2 and A\<^sub>1 and weak_basic_sim_tau_sequence by blast
  then obtain p\<^sub>2 where A\<^sub>7: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p\<^sub>2" and A\<^sub>8: "\<X> p\<^sub>2 q\<^sub>2" by auto
  then have "p\<^sub>2 \<leadsto>\<^sub>\<flat><\<X>> q\<^sub>2" using A\<^sub>8 and A\<^sub>1 by simp
  then obtain P\<^sub>3 where A\<^sub>9: "p\<^sub>2 \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P\<^sub>3 a" and A\<^sub>1\<^sub>0: "\<forall>a. \<X> (P\<^sub>3 a) (Q\<^sub>3 a)" using A\<^sub>5
    by (blast dest: weak_basic_sim_opening_elim)
  then have "\<exists>P. \<forall>a. P\<^sub>3 a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> P a \<and> \<X> (P a) (Q a)" using A\<^sub>6 and A\<^sub>1\<^sub>0 and A\<^sub>1 weak_basic_sim_tau_sequence2 by blast
  then obtain P where A\<^sub>1\<^sub>1: "\<And>a. P\<^sub>3 a \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> P a" and A\<^sub>1\<^sub>2: "\<And>a. \<X> (P a) (Q a)" by auto
  then have "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a" using A\<^sub>7 and A\<^sub>9 and A\<^sub>1\<^sub>1
    by (blast dest: prepend_tau_sequence_to_weak_tau_respecting_basic_transition_opening append_tau_sequence_to_weak_tau_respecting_basic_transition_opening)
  then show ?thesis using A\<^sub>1\<^sub>2 by auto
qed

lemma weak_basic_sim_transitivity:
  assumes A\<^sub>1: "q \<leadsto>\<^sub>\<flat><\<Y>> r"
  and     A\<^sub>2: "\<X> OO \<Y> \<le> \<Z>"
  and     A\<^sub>3: "is_weak_basic_sim \<X>"
  and     A\<^sub>4: "\<X> p q"
  shows "p \<leadsto>\<^sub>\<flat><\<Z>> r"
  using assms
proof -
  show ?thesis
  proof (induction rule: weak_basic_sim_cases)
    case (acting \<alpha> q')
    then have "r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'" by simp
    then obtain q\<^sub>2 where A\<^sub>5: "q \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q\<^sub>2" and A\<^sub>6: "\<Y> q\<^sub>2 q'" using A\<^sub>1 by (blast dest: weak_basic_sim_acting_elim)
    then have "\<exists>p'. p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p' \<and> \<X> p' q\<^sub>2" using A\<^sub>3 and A\<^sub>4 and A\<^sub>5 by (blast intro: weak_basic_sim_acting_elim2)
    then obtain p' where A\<^sub>7: "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> p'" and A\<^sub>8: "\<X> p' q\<^sub>2" by auto
    then have "\<Z> p' q'" using A\<^sub>8 and A\<^sub>6 and A\<^sub>2 by auto
    then show ?case using A\<^sub>7 by auto
  next
    case (opening Q)
    then have "r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" by simp
    then obtain Q' where A\<^sub>9: "q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q' a" and A\<^sub>1\<^sub>0: "\<forall>a. \<Y> (Q' a) (Q a)" using A\<^sub>1 by (blast dest: weak_basic_sim_opening_elim)
    then obtain P' where A\<^sub>1\<^sub>1: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P' a" and A\<^sub>1\<^sub>2: "\<forall>a. \<X> (P' a) (Q' a)"
      using A\<^sub>3 and A\<^sub>4 and A\<^sub>9 using weak_basic_sim_opening_elim2 by blast
    moreover have "\<forall>a. \<Z> (P' a) (Q a)" using A\<^sub>1\<^sub>2 and A\<^sub>1\<^sub>0 and `\<X> OO \<Y> \<le> \<Z>` by blast
    ultimately show ?case by blast
  qed
qed

(* TODO: Prove it. *)
lemma pre_weak_basic_receive_preservation: "(\<And>x. \<X> (P x) (Q x)) \<Longrightarrow> a \<triangleright>\<degree> x. P x \<leadsto>\<^sub>\<flat><\<X>> a \<triangleright>\<degree> x. Q x" sorry

(* TODO: Prove it. *)
lemma pre_left_weak_basic_parallel_preservation:
  assumes "p \<leadsto>\<^sub>\<flat><\<X>> q"
  and     "\<X> p q"
  and     "\<And>s t u. \<X> s t \<Longrightarrow> \<Y> (u \<parallel> s) (u \<parallel> t)"
  and     "\<And>S T. (\<And>x. \<Y> (S x) (T x)) \<Longrightarrow> \<Y> (\<nu>\<degree> x. S x) (\<nu>\<degree> x. T x)"
  shows   "r \<parallel> p \<leadsto>\<^sub>\<flat><\<Y>> r \<parallel> q"
  sorry

(* TODO: Prove it. *)
lemma pre_weak_basic_new_channel_preservation:
  assumes "\<And>x. P x \<leadsto>\<^sub>\<flat><\<X>> Q x"
  and     "\<And>R S y. (\<And>x. \<X> (R x) (S x)) \<Longrightarrow> \<Y> (\<nu>\<degree> y. R y) (\<nu>\<degree> y. S y)"
  and     "\<X> \<le> \<Y>"
  shows   "\<nu>\<degree> x. P x \<leadsto>\<^sub>\<flat><\<Y>> \<nu>\<degree> x. Q x"
  sorry

(** Weak basic bisimulation **)

lemma weak_basic_sim_monotonicity_aux [mono]: "\<X> \<le> \<Y> \<Longrightarrow> p \<leadsto>\<^sub>\<flat><\<X>> q \<longrightarrow> p \<leadsto>\<^sub>\<flat><\<Y>> q"
  by (auto intro: weak_basic_sim_monotonicity)

coinductive
  weak_basic_bisimilarity :: "process \<Rightarrow> process \<Rightarrow> bool" (infixr "\<approx>\<^sub>\<flat>" 50)
where
  step: "\<lbrakk> p \<leadsto>\<^sub>\<flat><(\<approx>\<^sub>\<flat>)> q; q \<approx>\<^sub>\<flat> p \<rbrakk> \<Longrightarrow> p \<approx>\<^sub>\<flat> q"

(*** Primitive inference rules (coinduction, introduction and elimination) ***)

(**** Up-to techniques for the bisimilarity proof method. ****)

(* Bisimulation up-to (strong) bisimilarity. *)

lemma weak_basic_bisim_up_to_strong_bisim[consumes 1, case_names sim sym]:
  assumes "\<X> p q"
  and     "\<And>r s. \<X> r s \<Longrightarrow> r \<leadsto>\<^sub>\<flat><((\<sim>\<^sub>\<flat>) OO \<X> OO (\<sim>\<^sub>\<flat>))> s"
  and     "\<And>r s. \<X> r s \<Longrightarrow> \<X> s r"
  shows   "p \<approx>\<^sub>\<flat> q"
  using assms
proof -
  have "(\<sim>\<^sub>\<flat>) OO \<X> OO (\<sim>\<^sub>\<flat>) \<le> (\<approx>\<^sub>\<flat>)" sorry (* TODO: Prove it. *)
  then show ?thesis
    using `\<X> p q` by blast 
qed

(**** Basic bisimilarity proof method. *****)

lemma weak_basic_bisim_proof_method_aux[consumes 1, case_names weak_basic_bisim, case_conclusion weak_basic_bisim step]:
  assumes related: "\<X> p q"
  and     step:    "\<And>p q. \<X> p q \<Longrightarrow> p \<leadsto>\<^sub>\<flat><\<X>> q \<and> \<X> q p"
  shows            "p \<approx>\<^sub>\<flat> q"
  using related
proof (coinduct rule: weak_basic_bisimilarity.coinduct)
  case weak_basic_bisimilarity
  then show ?case
    by (metis (no_types, lifting) local.step predicate2I weak_basic_sim_monotonicity_aux)
qed

lemma weak_basic_bisim_proof_method[consumes 1, case_names sim sym]:
  assumes "\<X> p q"
  and     "\<And>p q. \<X> p q \<Longrightarrow> p \<leadsto>\<^sub>\<flat><\<X>> q"
  and     "\<And>p q. \<X> p q \<Longrightarrow> \<X> q p"
  shows   "p \<approx>\<^sub>\<flat> q"
  using assms
by (coinduct rule: weak_basic_bisim_proof_method_aux) auto

(**** Elimination rules. *****)

lemma weak_basic_bisim_elim1: "p \<approx>\<^sub>\<flat> q \<Longrightarrow> p \<leadsto>\<^sub>\<flat><(\<approx>\<^sub>\<flat>)> q"
  by (auto dest: weak_basic_bisimilarity.cases)

lemma weak_basic_bisim_elim2: "p \<approx>\<^sub>\<flat> q \<Longrightarrow> q \<approx>\<^sub>\<flat> p"
  by (auto dest: weak_basic_bisimilarity.cases)

(**** Introduction rule. *****)

lemma weak_basic_bisim_intro: "\<lbrakk> p \<leadsto>\<^sub>\<flat><(\<approx>\<^sub>\<flat>)> q; q \<approx>\<^sub>\<flat> p \<rbrakk> \<Longrightarrow> p \<approx>\<^sub>\<flat> q"
  by (auto intro: weak_basic_bisimilarity.intros)

(*** Weak bisimilarity includes strong bisimilarity ***)

(* TODO: Prove it. *)
lemma strong_basic_sim_imp_weak_basic_sim: "p \<lesssim>\<^sub>\<flat> q \<Longrightarrow> p \<leadsto>\<^sub>\<flat><(\<approx>\<^sub>\<flat>)> q"
  sorry

(* TODO: Prove it. *)
lemma strong_basic_bisim_imp_weak_basic_bisim: "p \<sim>\<^sub>\<flat> q \<Longrightarrow> p \<approx>\<^sub>\<flat> q"
  sorry

(*** Weak bisimilarity is an equivalence relation ***)

lemma weak_basic_bisim_reflexivity: "p \<approx>\<^sub>\<flat> p"
proof -
  have "p = p" by simp
  then show ?thesis
    using weak_basic_bisim_proof_method and weak_basic_sim_reflexivity by blast
qed

lemma weak_basic_bisim_symmetry [sym]: "p \<approx>\<^sub>\<flat> q \<Longrightarrow> q \<approx>\<^sub>\<flat> p"
  using weak_basic_bisim_elim2 by auto

lemma weak_basic_bisim_transitivity [trans]: "\<lbrakk> p \<approx>\<^sub>\<flat> q; q \<approx>\<^sub>\<flat> r \<rbrakk> \<Longrightarrow> p \<approx>\<^sub>\<flat> r"
proof -
  assume "p \<approx>\<^sub>\<flat> q" and "q \<approx>\<^sub>\<flat> r"
  let ?\<X> = "(\<approx>\<^sub>\<flat>) OO (\<approx>\<^sub>\<flat>)"
  have "?\<X> p r" using \<open>p \<approx>\<^sub>\<flat> q\<close> and \<open>q \<approx>\<^sub>\<flat> r\<close> by blast
  then show ?thesis
  proof (coinduct rule: weak_basic_bisim_proof_method)
    case (sim p r)
    then obtain q where "p \<approx>\<^sub>\<flat> q" and "q \<approx>\<^sub>\<flat> r" using \<open>?\<X> p r\<close> by auto
    then have "q \<leadsto>\<^sub>\<flat><(\<approx>\<^sub>\<flat>)> r" using weak_basic_bisim_elim1 by auto
    moreover have "?\<X> \<le> ?\<X>" by simp
    ultimately show ?case using weak_basic_bisim_elim1 and weak_basic_sim_transitivity and \<open>p \<approx>\<^sub>\<flat> q\<close> by blast
  next
    case (sym p r)
    then show ?case using weak_basic_bisim_symmetry by auto
  qed
qed

(*** Preservation laws ***)
(* TODO: Prove them. *)

lemma weak_basic_receive_preservation: "(\<And>x. P x \<approx>\<^sub>\<flat> Q x) \<Longrightarrow> m \<triangleright> x. P x \<approx>\<^sub>\<flat> m \<triangleright> x. Q x" sorry
lemma weak_basic_parallel_preservation: "p \<approx>\<^sub>\<flat> q \<Longrightarrow> p \<parallel> r \<approx>\<^sub>\<flat> q \<parallel> r" sorry
lemma weak_basic_new_channel_preservation: "(\<And>a. P a \<approx>\<^sub>\<flat> Q a) \<Longrightarrow> \<nu> a. P a \<approx>\<^sub>\<flat> \<nu> a. Q a" sorry

(*** Structural congruence laws ***)

lemma weak_basic_parallel_scope_extension: "\<nu> a. P a \<parallel> q \<approx>\<^sub>\<flat> \<nu> a. (P a \<parallel> q)"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_parallel_scope_extension by simp

lemma weak_basic_new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<approx>\<^sub>\<flat> \<nu> a. \<nu> b. P a b"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_new_channel_scope_extension by simp

lemma weak_basic_parallel_unit: "\<zero> \<parallel> p \<approx>\<^sub>\<flat> p"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_parallel_unit by simp

lemma weak_basic_parallel_associativity: "(p \<parallel> q) \<parallel> r \<approx>\<^sub>\<flat> p \<parallel> (q \<parallel> r)"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_parallel_associativity by simp

lemma weak_basic_parallel_commutativity: "p \<parallel> q \<approx>\<^sub>\<flat> q \<parallel> p"
  using strong_basic_bisim_imp_weak_basic_bisim and basic_parallel_commutativity by simp

end
