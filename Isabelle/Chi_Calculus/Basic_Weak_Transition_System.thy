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

notation basic.weak.pre_bisimilarity (infix "\<lessapprox>\<^sub>\<flat>" 50)
notation basic.weak.bisimilarity (infix "\<approx>\<^sub>\<flat>" 50)

(* NOTE:
  This will become obsolete once there is only one locale interpretation for the strong transition
  system.
*)
lemma basic_strong_bisimilarity_in_weak_bisimilarity: "(\<sim>\<^sub>\<flat>) \<le> (\<approx>\<^sub>\<flat>)"
  sorry

lemma basic_weak_receive_preservation: "(\<And>x. P x \<approx>\<^sub>\<flat> Q x) \<Longrightarrow> a \<triangleright> x. P x \<approx>\<^sub>\<flat> a \<triangleright> x. Q x"
  sorry

lemma basic_weak_parallel_preservation_left: "p\<^sub>1 \<approx>\<^sub>\<flat> p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<parallel> q \<approx>\<^sub>\<flat> p\<^sub>2 \<parallel> q"
  sorry

lemma basic_weak_parallel_preservation_right: "q\<^sub>1 \<approx>\<^sub>\<flat> q\<^sub>2 \<Longrightarrow> p \<parallel> q\<^sub>1 \<approx>\<^sub>\<flat> p \<parallel> q\<^sub>2"
  sorry

lemma basic_weak_parallel_preservation: "\<lbrakk>p\<^sub>1 \<approx>\<^sub>\<flat> p\<^sub>2; q\<^sub>1 \<approx>\<^sub>\<flat> q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<approx>\<^sub>\<flat> p\<^sub>2 \<parallel> q\<^sub>2"
  sorry

lemma basic_weak_new_channel_preservation: "(\<And>a. P a \<approx>\<^sub>\<flat> Q a) \<Longrightarrow> \<nu> a. P a \<approx>\<^sub>\<flat> \<nu> a. Q a"
  sorry

lemma basic_weak_parallel_scope_extension_left: "\<nu> a. P a \<parallel> q \<approx>\<^sub>\<flat> \<nu> a. (P a \<parallel> q)"
  sorry

lemma basic_weak_parallel_scope_extension_right: "p \<parallel> \<nu> a. Q a \<approx>\<^sub>\<flat> \<nu> a. (p \<parallel> Q a)"
  sorry

lemma basic_weak_new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<approx>\<^sub>\<flat> \<nu> a. \<nu> b. P a b"
  sorry

lemma basic_weak_parallel_unit: "\<zero> \<parallel> p \<approx>\<^sub>\<flat> p"
  sorry

lemma basic_weak_parallel_commutativity: "p \<parallel> q \<approx>\<^sub>\<flat> q \<parallel> p"
  sorry

lemma basic_weak_parallel_associativity: "(p \<parallel> q) \<parallel> r \<approx>\<^sub>\<flat> p \<parallel> (q \<parallel> r)"
  sorry

end
