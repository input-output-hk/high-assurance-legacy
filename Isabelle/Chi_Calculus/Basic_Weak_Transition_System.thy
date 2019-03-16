section \<open>Basic Weak Transition System\<close>

theory Basic_Weak_Transition_System
  imports
    Transition_Systems.Std_Weak_Residuals
    Transition_Systems.Weak_Transition_Systems
    Basic_Transition_System
begin

inductive basic_silent :: "[process, process basic_residual] \<Rightarrow> bool" where
  basic_internal_is_silent: "basic_silent p (\<lbrace>\<tau>\<rbrace> p)"

interpretation basic: std_weak_residual rel_basic_residual basic_silent
proof
  show "basic_silent OO basic_silent\<inverse>\<inverse> = (=)"
    by (blast elim: basic_silent.cases intro: basic_silent.intros)
next
  show "basic_silent\<inverse>\<inverse> OO basic_silent \<le> (=)"
    by (blast elim: basic_silent.cases)
next
  fix \<X>
  show "\<X> OO basic_silent = basic_silent OO rel_basic_residual \<X>"
  proof (intro ext, intro iffI)
    fix p and c
    assume "(\<X> OO basic_silent) p c"
    then show "(basic_silent OO rel_basic_residual \<X>) p c"
      by (blast elim: basic_silent.cases intro: basic_silent.intros basic_residual.rel_intros(1))
  next
    fix p and c
    assume "(basic_silent OO rel_basic_residual \<X>) p c"
    then show "(\<X> OO basic_silent) p c"
      by (blast elim: basic_silent.cases basic_residual.rel_cases intro: basic_silent.intros)
  qed
qed

interpretation basic: weak_transition_system basic_silent basic.absorb basic_transition
  by intro_locales

(* Basic weak transition \<Rightarrow>\<^sub>\<flat> *)

notation basic.weak_transition (infix "\<Rightarrow>\<^sub>\<flat>" 50)

(* Sequence of basic silent transitions: \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> *)

abbreviation
  basic_silent_sequence :: "[process, process] \<Rightarrow> bool" (infix "\<Rightarrow>\<^sup>\<tau>\<^sub>\<flat>" 50)
where
  "basic_silent_sequence p q \<equiv> p \<Rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q"

lemma basic_silent_sequence_refl: "p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> p"
  by (simp add: basic.silent_transition basic_internal_is_silent)

lemma basic_silent_sequence_trans [trans]: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r; r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q \<rbrakk> \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  by (blast intro: basic.composed_transition basic_internal_is_silent)

lemma basic_silent_sequence_non_empty: "\<lbrakk> p \<Rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q; p \<noteq> q \<rbrakk> \<Longrightarrow> \<exists>r. p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r \<and> r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
proof -
  fix p q
  assume "p \<Rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q" and "p \<noteq> q"
  from \<open>p \<Rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q\<close> and \<open>p \<noteq> q\<close> show "\<exists>r. p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r \<and> r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  proof (induction "\<lbrace>\<tau>\<rbrace> q" arbitrary: q)
    case (strong_transition p)
    then have "q \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
      using basic_silent_sequence_refl by simp
    moreover have "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q"
      by (blast intro: strong_transition.hyps strong_transition.prems)
    ultimately show ?case
      by fastforce
  next
    case (silent_transition p)
    then show ?case
      by (blast elim: basic_silent.cases)
  next
    case (composed_transition p c)
    let ?\<I> = "\<lambda>p\<^sub>1 c\<^sub>1. p\<^sub>1 \<Rightarrow>\<^sub>\<flat> c\<^sub>1 \<and> (\<forall>q\<^sub>1. c\<^sub>1 = \<lbrace>\<tau>\<rbrace> q\<^sub>1 \<longrightarrow> p\<^sub>1 \<noteq> q\<^sub>1 \<longrightarrow> (\<exists>r. p\<^sub>1 \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r \<and> r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q\<^sub>1))"
    have "(basic.absorb_downward ?\<I> \<squnion> basic.absorb_upward ?\<I>) c (\<lbrace>\<tau>\<rbrace> q)"
      using composed_transition.hyps(3) by blast
    then have "basic.absorb_downward ?\<I> c (\<lbrace>\<tau>\<rbrace> q) \<squnion> basic.absorb_upward ?\<I> c (\<lbrace>\<tau>\<rbrace> q)"
      by simp
    then show ?case
    proof (elim sup_boolE)
      assume "basic.absorb_downward ?\<I> c (\<lbrace>\<tau>\<rbrace> q)"
      then obtain p\<^sub>1 where "c = \<lbrace>\<tau>\<rbrace> p\<^sub>1" and "p\<^sub>1 \<Rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<and> (p\<^sub>1 \<noteq> q \<longrightarrow> (\<exists>r. p\<^sub>1 \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r \<and> r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q))"
        using basic_silent.simps by blast
      then have "p\<^sub>1 \<Rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<and> (p\<^sub>1 \<noteq> q \<longrightarrow> (\<exists>r. p\<^sub>1 \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r \<and> r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q))"
        using \<open>p \<noteq> q\<close> by simp
      then show ?case
        using \<open>c = \<lbrace>\<tau>\<rbrace> p\<^sub>1\<close> and composed_transition.hyps(2) and composed_transition.prems and basic_silent_sequence_trans
        by blast
    next
      assume "basic.absorb_upward ?\<I> c (\<lbrace>\<tau>\<rbrace> q)"
      then obtain p\<^sub>1 where "c = \<lbrace>\<tau>\<rbrace> p\<^sub>1" and "p\<^sub>1 \<Rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<and> (p\<^sub>1 \<noteq> q \<longrightarrow> (\<exists>r. p\<^sub>1 \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> r \<and> r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q))"
        by (fastforce elim: basic_residual.rel_cases basic_silent.cases)
      then show ?thesis
        using composed_transition.hyps(2) and composed_transition.prems and basic_silent_sequence_trans
        by blast
    qed
  qed
qed

lemma basic_weak_transition_acting_elim: "p \<Rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<Longrightarrow> \<exists>r s. p \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> r \<and> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> s \<and> s \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q" sorry

(* Lifted basic weak operational semantics *)

lemma basic_weak_transition_sending: "a \<triangleleft> x \<Rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<zero>"
  using sending by (simp add: basic.strong_transition)

lemma basic_weak_transition_receiving: "a \<triangleright> x. P x \<Rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> P x"
  using receiving by (simp add: basic.strong_transition)

(** Basic weak simulating transition \<Rightarrow>\<^sub>\<flat>\<^sup>^ **)

inductive
  basic_weak_simulating_transition :: "process \<Rightarrow> process basic_residual \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>\<flat>\<^sup>^" 50)
where
  basic_weak_simulating_transition_acting: "p \<Rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q \<or> (\<alpha> = \<tau> \<and> p = q) \<Longrightarrow> p \<Rightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<alpha>\<rbrace> q" |
  basic_weak_simulating_transition_opening: "p \<Rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<Longrightarrow> p \<Rightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<nu> a\<rbrace> P a"

(** Lifted basic weak simulating operational semantics **)

lemma basic_weak_simulating_sending: "a \<triangleleft> x \<Rightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>a \<triangleleft> x\<rbrace> \<zero>"
  by (simp add: basic_weak_transition_sending basic_weak_simulating_transition_acting)

lemma basic_weak_simulating_receiving: "a \<triangleright> x. P x \<Rightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>a \<triangleright> x\<rbrace> P x"
  by (simp add: basic_weak_transition_receiving basic_weak_simulating_transition_acting)

end
