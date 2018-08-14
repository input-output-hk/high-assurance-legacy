theory Basic_Weak_Bisimulation
  imports Basic_Transition_System
begin

(* Sequence of \<tau>-transitions *)

abbreviation tau_sequence :: "
    ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
  ("_ \<turnstile> _ \<Longrightarrow>\<^sub>\<flat> _" [51, 0, 51] 50)
where
  "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> Q \<equiv> (P, Q) \<in> {(P, Q) | P Q. \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q}^*"

lemma tau_sequence_refl: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> P" 
  by simp

lemma tau_sequence_trans: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> Q"
  by simp

lemma tau_transition_is_tau_sequence: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> Q" 
  by auto

lemma append_tau_transition_to_tau_sequence_is_tau_sequence:  "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> Q"
  by (metis (mono_tags, lifting) mem_Collect_eq rtrancl.simps)

lemma prepend_tau_transition_to_tau_sequence_is_tau_sequence: "\<lbrakk> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> Q"
  by (simp add: rtrancl_into_trancl2 trancl_into_rtrancl) 

lemma tau_sequence_induction[consumes 1, case_names tau_seq_refl tau_seq_step]:
  assumes "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> Q"
  and     "\<PP> P"
  and     "\<And>R S. \<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S; \<PP> R \<rbrakk> \<Longrightarrow> \<PP> S"
  shows   "\<PP> Q"
  using assms
  by (induction rule: rtrancl_induct) auto 

(** \<tau>-sequence relation behaves as expected w.r.t. process operators (except, of course, \<triangleright> and \<triangleleft>) **)

lemma tau_sequence_par_left: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> P' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat> P' \<parallel> Q"
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

lemma tau_sequence_par_right: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat> Q' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat> P \<parallel> Q'"
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

lemma tau_sequence_par: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> P'; \<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat> Q' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat> P' \<parallel> Q'"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> P'" and "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat> Q'" 
  have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat> P' \<parallel> Q"
    using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> P'\<close> and tau_sequence_par_left by simp
  moreover have "\<Gamma> \<turnstile> P' \<parallel> Q \<Longrightarrow>\<^sub>\<flat> P' \<parallel> Q'"
    using \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat> Q'\<close> and tau_sequence_par_right by simp 
  finally show ?thesis 
    by simp
qed 

lemma tau_sequence_res: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> P' \<Longrightarrow> \<Gamma> \<turnstile> \<nu> a. P \<Longrightarrow>\<^sub>\<flat> \<nu> a. P'"
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

(* Weak basic transition \<Longrightarrow>\<^sub>\<flat>R *)

definition 
  weak_basic_transition :: "
    ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) basic_residual \<Rightarrow>
    bool"
  ("_ \<turnstile> _ \<Longrightarrow>\<^sub>\<flat>_" [51, 0, 51] 50)
  where
   "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>C \<equiv> 
      case C of 
        \<lbrace>\<alpha>\<rbrace> Q     \<Rightarrow> \<exists>R S. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<and> \<Gamma> \<turnstile> S \<Longrightarrow>\<^sub>\<flat> Q |
        Opening \<F> \<Rightarrow> \<exists>R \<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sub>\<flat> \<F> a)"

lemma weak_basic_transition_acting_intro: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S; \<Gamma> \<turnstile> S \<Longrightarrow>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  using weak_basic_transition_def by force 

lemma weak_basic_transition_scoping_intro: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a; \<And>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sub>\<flat> \<Q> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  using weak_basic_transition_def by force 

lemma weak_basic_transition_acting_elim: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<exists>R S. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<and> \<Gamma> \<turnstile> S \<Longrightarrow>\<^sub>\<flat> Q"
  by (simp split: basic_residual.split add: weak_basic_transition_def)

lemma weak_basic_transition_scoping_elim: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<exists>R \<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sub>\<flat> \<Q> a)"
  by (simp split: basic_residual.split add: weak_basic_transition_def)

lemma weak_basic_transition_single_acting: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  using weak_basic_transition_acting_intro by blast 

lemma weak_basic_transition_single_scoping: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  using weak_basic_transition_scoping_intro by blast

end
