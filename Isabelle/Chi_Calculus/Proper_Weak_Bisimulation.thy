theory Proper_Weak_Bisimulation
  imports Typed_Proper_Transition_System Basic_Weak_Bisimulation
begin

lemma proper_tau_trans_is_basic_tau_trans: "(p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q) = (p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q)"
  by (metis basic_action_of.simps(2) proper_residual.distinct(1) proper_residual.inject(1) proper_transition.simps)

lemma proper_simple_trans_is_basic_trans: "p \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<Longrightarrow> p \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q"
  by (metis proper_residual.distinct(1) proper_residual.inject(1) proper_transition.simps)

(* TODO: Rename \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> to \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> in `Basic_Weak_Bisimulation`, then remove the following abbreviation. *)
abbreviation
  proper_tau_sequence :: "process \<Rightarrow> process \<Rightarrow> bool" (infix "\<Rightarrow>\<^sup>\<tau>" 50)
where
  "(\<Rightarrow>\<^sup>\<tau>) \<equiv> (\<Rightarrow>\<^sup>\<tau>\<^sub>\<flat>)"

(* Weak Semantics *)

(** Weak \<tau>-respecting proper transition \<Longrightarrow>\<^sub>\<sharp> c **)

inductive
  weak_tau_respecting_proper_transition :: "process \<Rightarrow> proper_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<sharp>" 50)
where
  simple:
    "\<exists>r s. p \<Rightarrow>\<^sup>\<tau> r \<and> r \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> s \<and> s \<Rightarrow>\<^sup>\<tau> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" |
  output_without_opening:
    "\<exists>r s. p \<Rightarrow>\<^sup>\<tau> r \<and> r \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> s \<and> s \<Rightarrow>\<^sup>\<tau> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q" |
  output_with_opening:
    "\<exists>Q. p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b \<and> (\<forall>b. Q b \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> K b) \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. K b"

(*** NOTE: \<tau>-prefix simulation, just to be used in examples. ***)
abbreviation
  tau_prefix :: "process \<Rightarrow> process"
where
  "tau_prefix p \<equiv> \<nu> x. (x \<triangleleft> undefined \<parallel> x \<triangleright> _. p)"

syntax
  "_tau_prefix" :: "process \<Rightarrow> process" ("(3\<tau>./ _)" [100] 100)
translations
  "\<tau>. p" \<rightleftharpoons> "CONST tau_prefix p"

lemma tau_prefix_transition: "\<tau>. p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> x. (\<zero> \<parallel> p)"
proof -
  have A: "\<tau>. p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> x\<rbrace> x \<triangleleft> undefined \<parallel> x \<triangleright> _. p"
    using opening by simp
  moreover have "\<And>x. x \<triangleleft> undefined \<rightarrow>\<^sub>\<flat>\<lbrace>x \<triangleleft> undefined\<rbrace> \<zero>"
    using sending by simp
  moreover have "\<And>x. x \<triangleright> _. p \<rightarrow>\<^sub>\<flat>\<lbrace>x \<triangleright> undefined\<rbrace> p"
    using receiving by blast
  ultimately have "\<And>x. x \<triangleleft> undefined \<parallel> x \<triangleright> _. p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> p"
    using communication ltr by blast
  then show ?thesis using scoped_acting and A by simp
qed

lemma "\<nu>\<degree> x. a \<triangleleft>\<degree> x \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree> x\<rbrace> a \<triangleleft>\<degree> x"
  by (simp add: weak_tau_respecting_basic_transition_opening)

lemma "\<And>x. a \<triangleleft>\<degree> x \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft>\<degree> x\<rparr> \<zero>"
  using
    proper_transition.output_without_opening and
    typed_sending and
    weak_tau_respecting_proper_transition.output_without_opening
  by fastforce

lemma "\<And>x. a \<triangleleft> x \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
proof -
  have "\<And>x. a \<triangleleft> x \<parallel> \<tau>. \<zero> \<Rightarrow>\<^sup>\<tau> a \<triangleleft> x \<parallel> \<tau>. \<zero>"
    by simp
  moreover have "\<And>x. a \<triangleleft> x \<parallel> \<tau>. \<zero> \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<zero> \<parallel> \<tau>. \<zero>"
  proof -
    have "\<And>x. a \<triangleleft> x \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<zero>"
      using sending by simp
    then have "\<And>x. a \<triangleleft> x \<parallel> \<tau>. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<zero> \<parallel> \<tau>. \<zero>"
      using acting_left by simp
    then show "\<And>x. a \<triangleleft> x \<parallel> \<tau>. \<zero> \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<zero> \<parallel> \<tau>. \<zero>"
      using proper_transition.output_without_opening by simp
  qed
  moreover have "\<zero> \<parallel> \<tau>. \<zero> \<Rightarrow>\<^sup>\<tau> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
  proof -
    have "\<tau>. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> z. (\<zero> \<parallel> \<zero>)"
      using tau_prefix_transition by simp
    then have "\<zero> \<parallel> \<tau>. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
      using acting_right by simp
    then show "\<zero> \<parallel> \<tau>. \<zero> \<Rightarrow>\<^sup>\<tau> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
      using tau_transition_is_tau_sequence by simp
  qed
  ultimately show "\<And>x. a \<triangleleft> x \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
    using weak_tau_respecting_proper_transition.output_without_opening by fastforce
qed

(* TODO: Prove it. *)
lemma "\<nu>\<degree> x. a \<triangleleft>\<degree> x \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft>\<degree> \<nu>\<degree> x. x\<rparr> \<zero> \<parallel> \<nu>\<degree> z. (\<zero> \<parallel> \<zero>)" sorry

(* TODO: Prove it. *)
lemma lem5: "\<nu>\<degree> x y. a \<triangleleft>\<degree> (x, y) \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft>\<degree> \<nu>\<degree> x y. (x, y)\<rparr> \<zero> \<parallel> \<nu>\<degree> z. (\<zero> \<parallel> \<zero>)" sorry

(*** Intro rules ***)

lemma weak_tau_respecting_proper_transition_simple_intro: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau> r; r \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> s; s \<Rightarrow>\<^sup>\<tau> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q"
  using weak_tau_respecting_proper_transition.simple by fastforce

lemma weak_tau_respecting_proper_transition_output_without_opening_intro: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau> r; r \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> s; s \<Rightarrow>\<^sup>\<tau> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q"
  using weak_tau_respecting_proper_transition.output_without_opening by fastforce

lemma weak_tau_respecting_proper_transition_output_with_opening_intro: "\<lbrakk> p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b; \<And>b. Q b \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> K b \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. K b"
  using weak_tau_respecting_proper_transition.output_with_opening by fastforce

(*** Elim rules ***)

lemma weak_tau_respecting_proper_transition_simple_elim: "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<Longrightarrow> \<exists>r s. p \<Rightarrow>\<^sup>\<tau> r \<and> r \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> s \<and> s \<Rightarrow>\<^sup>\<tau> q"
proof (induction p "\<lparr>\<delta>\<rparr> q" rule: weak_tau_respecting_proper_transition.induct)
  case simple
  then show ?case by simp
qed

lemma weak_tau_respecting_proper_transition_output_without_opening_elim: "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q \<Longrightarrow> \<exists>r s. p \<Rightarrow>\<^sup>\<tau> r \<and> r \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> s \<and> s \<Rightarrow>\<^sup>\<tau> q"
proof (induction p "\<lparr>a \<triangleleft> x\<rparr> q" rule: weak_tau_respecting_proper_transition.induct)
  case output_without_opening
  then show ?case by simp
qed

lemma weak_tau_respecting_proper_transition_output_with_opening_elim: "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. K b \<Longrightarrow> \<exists>Q. p \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b \<and> (\<forall>b. Q b \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> K b)"
proof (induction p "\<lparr>a \<triangleleft> \<nu> b. K b" arbitrary: K rule: weak_tau_respecting_proper_transition.induct)
  case output_with_opening
  then show ?case by auto
qed

(*** Strong to weak transitions ***)

lemma weak_tau_respecting_proper_transition_single_simple: "p \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q"
  using weak_tau_respecting_proper_transition_simple_intro by blast

lemma weak_tau_respecting_proper_transition_single_output_without_opening: "p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q"
  using weak_tau_respecting_proper_transition_output_without_opening_intro by blast

lemma weak_tau_respecting_proper_transition_single_output_with_opening: "p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. K b \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. K b"
proof (induction p "\<lparr>a \<triangleleft> \<nu> b. K b" arbitrary: K rule: proper_transition.induct)
  case (output_with_opening p Q K)
  then show ?case
   (* TODO: Find a better proof. *)
    by (metis
         proper_residual.inject(2)
         proper_transition.cases
         weak_tau_respecting_basic_transition_single_opening
         weak_tau_respecting_proper_transition.output_with_opening
         weak_tau_respecting_proper_transition_single_output_without_opening
         weak_tau_respecting_proper_transition_single_simple)
qed

(*** Other lemmas ***)

lemma weak_tau_respecting_proper_transition_tau: "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q"
  then obtain r and s where "p \<Rightarrow>\<^sup>\<tau> r" and "r \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> s" and "s \<Rightarrow>\<^sup>\<tau> q"
    using weak_tau_respecting_proper_transition_simple_elim by fastforce
  then have "r \<Rightarrow>\<^sup>\<tau> s" using \<open>r \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> s\<close> and tau_transition_is_tau_sequence and proper_tau_trans_is_basic_tau_trans by simp
  then show ?thesis using \<open>p \<Rightarrow>\<^sup>\<tau> r\<close> and \<open>s \<Rightarrow>\<^sup>\<tau> q\<close> by (simp add: tau_sequence_trans)
qed

lemma prepend_tau_sequence_to_weak_tau_respecting_proper_transition_simple: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau> r; r \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q"
  (* TODO: Find a better proof (see `prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting`) *)
  by (metis (no_types, lifting) tau_sequence_trans weak_tau_respecting_proper_transition_simple_elim weak_tau_respecting_proper_transition_simple_intro)

lemma prepend_tau_sequence_to_weak_tau_respecting_proper_transition_output_without_opening: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau> r; r \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q"
  (* TODO: Find a better proof. *)
  by (smt rtrancl_trans weak_tau_respecting_proper_transition.output_without_opening weak_tau_respecting_proper_transition_output_without_opening_elim)

lemma prepend_tau_sequence_to_weak_tau_respecting_proper_transition_output_with_opening: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau> r; r \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> a. K a \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> a. K a"
  (* TODO: Find a better proof. *)
  by (metis (no_types, lifting) prepend_tau_sequence_to_weak_tau_respecting_basic_transition_opening weak_tau_respecting_proper_transition.output_with_opening weak_tau_respecting_proper_transition_output_with_opening_elim)

lemma append_tau_sequence_to_weak_tau_respecting_proper_transition_simple: "\<lbrakk> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> r; r \<Rightarrow>\<^sup>\<tau> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q"
  (* TODO: Find a better proof (see `append_tau_sequence_to_weak_tau_respecting_basic_transition_acting`) *)
  by (metis (no_types, lifting) converse_rtrancl_into_rtrancl rtrancl_idemp weak_tau_respecting_proper_transition.simple weak_tau_respecting_proper_transition_simple_elim)

lemma append_tau_sequence_to_weak_tau_respecting_proper_transition_output_without_opening: "\<lbrakk> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> r; r \<Rightarrow>\<^sup>\<tau> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q"
  (* TODO: Find a better proof. *)
  by (metis (no_types, lifting) tau_sequence_trans weak_tau_respecting_proper_transition_output_without_opening_elim weak_tau_respecting_proper_transition_output_without_opening_intro)

(* NOTE: Check that a lemma like the following lemma makes some sense.
lemma append_tau_sequence_to_weak_tau_respecting_proper_transition_output_with_opening: "\<lbrakk> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> a. K a; ? \<Rightarrow>\<^sup>\<tau> q \<rbrakk> \<Longrightarrow> ?"
*)

(** Lifted weak \<tau>-respecting proper operational semantics **)

lemma weak_tau_respecting_proper_transition_simple: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q"
  (* TODO: Find a better proof. *)
  using proper_transition.simple weak_tau_respecting_basic_transition_acting_elim weak_tau_respecting_proper_transition_simple_intro by blast

lemma weak_tau_respecting_proper_transition_output_without_opening: "p \<Longrightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q"
  (* TODO: Find a better proof. *)
  using output_without_opening weak_tau_respecting_basic_transition_acting_elim weak_tau_respecting_proper_transition_output_without_opening_intro sorry

(** Weak proper transition \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ **)

definition weak_proper_transition :: "process \<Rightarrow> proper_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<sharp>\<^sup>^" 50)
  where
   "p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ c \<equiv>
      case c of
        \<lparr>\<delta>\<rparr> q \<Rightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<or> (\<delta> = \<tau> \<and> p = q) |
        \<lparr>a \<triangleleft> x\<rparr> q \<Rightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q |
        Output a K \<Rightarrow> p \<Longrightarrow>\<^sub>\<sharp> Output a K"

lemma prepend_tau_transition_to_weak_proper_transition: "\<lbrakk> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> r; r \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
proof -
  assume "p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> r" and "r \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
  then have "r \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<or> \<delta> = \<tau> \<and> r = q"
    by (simp add: weak_proper_transition_def)
  then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<or> \<delta> = \<tau> \<and> p = q"
    using
      \<open>p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> r\<close> and
      prepend_tau_sequence_to_weak_tau_respecting_proper_transition_simple and
      weak_tau_respecting_proper_transition_single_simple and
      weak_tau_respecting_proper_transition_tau
    by meson
  then show ?thesis
    by (simp add: weak_proper_transition_def)
qed

lemma append_tau_transition_to_weak_proper_transition: "\<lbrakk> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> r; r \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> r" and "r \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q"
  then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> r \<or> \<delta> = \<tau> \<and> p = r"
    by (simp add: weak_proper_transition_def)
  then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<or> \<delta> = \<tau> \<and> p = q"
    using
      \<open>r \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q\<close> and
      append_tau_sequence_to_weak_tau_respecting_proper_transition_simple and
      weak_tau_respecting_proper_transition_single_simple and
      weak_tau_respecting_proper_transition_tau
    by meson
  then show ?thesis
    by (simp add: weak_proper_transition_def)
qed

lemma tau_sequence_is_weak_proper_tau_transition: "p \<Rightarrow>\<^sup>\<tau> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by (simp add: weak_proper_transition_def)
next
  case (tau_seq_step r s)
  then show ?case
    using append_tau_transition_to_weak_proper_transition and proper_transition.simple by auto
qed

lemma weak_proper_tau_transition_is_tau_sequence: "p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> q \<Longrightarrow> p \<Rightarrow>\<^sup>\<tau> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> q"
  then show ?thesis
  proof (cases "p = q")
    case True
    then show ?thesis by (simp add: tau_sequence_refl)
  next
    case False
    then have " p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q" using \<open>p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> q\<close> and weak_proper_transition_def by force
    then show ?thesis using weak_tau_respecting_proper_transition_tau by fastforce
  qed
qed

lemma weak_proper_transition_refl_intro: "p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> p"
  by (simp add: weak_proper_transition_def)

lemma weak_proper_transition_step_intro: "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
  by (simp add: weak_proper_transition_def)

lemma weak_proper_transition_step_elim: "\<lbrakk> p \<noteq> q; p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q"
  by (simp add: weak_proper_transition_def)

lemma weak_proper_transition_induction
  [consumes 1, case_names weak_proper_tran_refl weak_proper_tran_step]:
  assumes "p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
  and     "\<PP> ProperInternal p"
  and     "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<Longrightarrow> \<PP> \<delta> q"
  shows   "\<PP> \<delta> q"
  using assms
  by (auto simp add: weak_proper_transition_def)

lemma weak_proper_transition_single_simple: "p \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
  using weak_tau_respecting_proper_transition_simple_intro and weak_proper_transition_step_intro by fastforce

lemma weak_proper_transition_single_output_without_opening: "p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleleft> x\<rparr> q"
  using weak_proper_transition_def and weak_tau_respecting_proper_transition_single_output_without_opening by simp

lemma prepend_tau_sequence_to_weak_proper_transition: "\<lbrakk> p \<Rightarrow>\<^sup>\<tau> r; r \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
proof -
  assume "p \<Rightarrow>\<^sup>\<tau> r" and "r \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
  then show ?thesis
  proof (cases "r = q")
    case True
    then have A1: "p \<Rightarrow>\<^sup>\<tau> q" using \<open>p \<Rightarrow>\<^sup>\<tau> r\<close> and True by simp
    moreover have A2: "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q" using \<open>r \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<delta> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_proper_tau_transition)
    next
      case False
      then have "q \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" using A2 and False by (simp add: weak_proper_transition_def)
      then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" using A1 by (simp add: prepend_tau_sequence_to_weak_tau_respecting_proper_transition_simple)
      then show ?thesis by (simp add: weak_proper_transition_step_intro)
    qed
  next
    case False
    then have "r \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" using \<open>r \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q\<close> by (simp add: weak_proper_transition_step_elim)
    then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" using \<open>p \<Rightarrow>\<^sup>\<tau> r\<close> and prepend_tau_sequence_to_weak_tau_respecting_proper_transition_simple by simp
    then show ?thesis by (simp add: weak_proper_transition_step_intro)
  qed
qed

lemma append_tau_sequence_to_weak_proper_transition: "\<lbrakk> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> r; r \<Rightarrow>\<^sup>\<tau> q \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
proof -
  assume "p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> r" and "r \<Rightarrow>\<^sup>\<tau>\<^sub>\<flat> q"
  then show ?thesis
  proof (cases "p = r")
    case True
    then have A1: "p \<Rightarrow>\<^sup>\<tau> q" using \<open>r \<Rightarrow>\<^sup>\<tau> q\<close> and True by simp
    moreover have A2: "p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> p" using \<open>p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> r\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<delta> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_proper_tau_transition)
    next
      case False
      then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> p" using A2 and False by (simp add: weak_proper_transition_def)
      then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" using A1 by (simp add: append_tau_sequence_to_weak_tau_respecting_proper_transition_simple)
      then show ?thesis by (simp add: weak_proper_transition_step_intro)
    qed
  next
    case False
    then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> r" using \<open>p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> r\<close> by (simp add: weak_proper_transition_step_elim)
    then have "p \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" using \<open>r \<Rightarrow>\<^sup>\<tau> q\<close> and append_tau_sequence_to_weak_tau_respecting_proper_transition_simple by simp
    then show ?thesis by (simp add: weak_proper_transition_step_intro)
  qed
qed

(** Lifted weak proper operational semantics **)

lemma weak_proper_transition_simple: "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>basic_action_of \<delta>\<rbrace> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> q"
  (* TODO: Find a nicer proof. *)
  by (smt basic_action.distinct(1) basic_action_of.simps(1) basic_residual.simps(5) proper_action.exhaust proper_residual.simps(5) weak_basic_transition_def weak_proper_transition_def weak_tau_respecting_proper_transition_simple)

lemma weak_proper_transition_output_without_opening: "p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>a \<triangleleft> x\<rbrace> q \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleleft> x\<rparr> q"
  by (simp add: weak_basic_transition_def weak_proper_transition_def weak_tau_respecting_proper_transition_output_without_opening)

lemma weak_proper_transition_output_with_opening: "\<lbrakk> p \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<nu> b\<rbrace> Q b; \<And>b. Q b \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleleft> K b \<rbrakk> \<Longrightarrow> p \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleleft> \<nu> b. K b"
  (* TODO: Find a nicer proof. *)
  by (smt basic_residual.simps(6) output_rest.exhaust output_rest.simps(5) output_rest.simps(6) proper_residual.simps(6) weak_basic_transition_def weak_proper_transition_def weak_tau_respecting_proper_transition.output_with_opening)

(** Misc proofs **)

lemma weak_proper_transition_sending: "a \<triangleleft> x \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleleft> x\<rparr> \<zero>"
proof -
  have "a \<triangleleft> x \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<zero>"
  proof -
    have "a \<triangleleft> x \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<zero>" using sending by simp
    then have "a \<triangleleft> x \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<zero>" using proper_transition.output_without_opening by simp
    then show ?thesis using weak_tau_respecting_proper_transition_single_output_without_opening by simp
  qed
  then show ?thesis by (simp add: weak_proper_transition_def)
qed

lemma weak_proper_transition_receiving: "a \<triangleright> x. P x \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleright> x\<rparr> P x"
proof -
  have "a \<triangleright> x. P x \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> P x"
    using receiving by simp
  then have "a \<triangleright> x. P x \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> P x"
    using proper_transition.simple by simp
  then show ?thesis
    using weak_proper_transition_single_simple by simp
qed

(* Weak proper bisimilarity *)

(** Weak proper simulation **)

abbreviation
  weak_proper_simulation :: "process \<Rightarrow> (process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> process \<Rightarrow> bool"
  ("_ \<leadsto>\<^sub>\<sharp><_> _" [50, 50, 50] 50)
where
  "p \<leadsto>\<^sub>\<sharp><\<X>> q \<equiv> \<forall>c. p \<rightarrow>\<^sub>\<sharp> c \<longrightarrow> (\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift \<X> c d)"

abbreviation
  is_weak_proper_sim
where
  "is_weak_proper_sim \<X> \<equiv> \<forall>p q. \<X> p q \<longrightarrow> p \<leadsto>\<^sub>\<sharp><\<X>> q"

lemma weak_proper_sim_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><\<X>> q \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><\<Y>> q"
  by (meson predicate2D proper.lift_monotonicity)

(*** Introduction and elimination rules. ***)

(* TODO: Is this needed? *)
lemma weak_proper_sim_intro: "(\<And>c. p \<rightarrow>\<^sub>\<sharp> c \<and> (\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift \<X> c d)) \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><\<X>> q"
  by simp

(* TODO: Is this needed? *)
lemma weak_proper_sim_elim: "\<lbrakk> p \<leadsto>\<^sub>\<sharp><\<X>> q; p \<rightarrow>\<^sub>\<sharp> c \<rbrakk> \<Longrightarrow> \<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift \<X> c d"
  by simp

(*** Simulation is a pre-order relation. ***)

(* TODO: Prove it. *)
lemma weak_proper_sim_reflexivity: "(\<And>p. \<X> p p) \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><\<X>> p" sorry

(* TODO: Prove it. *)
lemma weak_proper_sim_transitivity:
  assumes A\<^sub>1: "q \<leadsto>\<^sub>\<sharp><\<Y>> r"
  and     A\<^sub>2: "\<X> OO \<Y> \<le> \<Z>"
  and     A\<^sub>3: "is_weak_proper_sim \<X>"
  and     A\<^sub>4: "\<X> p q"
  shows "p \<leadsto>\<^sub>\<sharp><\<Z>> r"
  sorry

(*** Preservation laws for simulation. ***)

(* TODO: Prove it. *)
lemma pre_weak_proper_receive_preservation: "(\<And>x. \<X> (P x) (Q x)) \<Longrightarrow> a \<triangleright>\<degree> x. P x \<leadsto>\<^sub>\<sharp><\<X>> a \<triangleright>\<degree> x. Q x" sorry

(* TODO: Prove it. *)
lemma pre_left_weak_proper_parallel_preservation:
  assumes "p \<leadsto>\<^sub>\<sharp><\<X>> q"
  and     "\<X> p q"
  and     "\<And>s t u. \<X> s t \<Longrightarrow> \<Y> (u \<parallel> s) (u \<parallel> t)"
  and     "\<And>S T. (\<And>x. \<Y> (S x) (T x)) \<Longrightarrow> \<Y> (NewChannel S) (NewChannel T)"
  shows   "r \<parallel> p \<leadsto>\<^sub>\<sharp><\<Y>> r \<parallel> q"
  sorry

(* TODO: Prove it. *)
lemma pre_weak_proper_new_channel_preservation:
  assumes "\<And>x. P x \<leadsto>\<^sub>\<sharp><\<X>> Q x"
  and     "\<And>R S y. (\<And>x. \<X> (R x) (S x)) \<Longrightarrow> \<Y> (NewChannel R) (NewChannel S)"
  and     "\<X> \<le> \<Y>"
  shows   "NewChannel P \<leadsto>\<^sub>\<sharp><\<Y>> NewChannel Q"
  sorry

(** Weak proper bisimulation **)

lemma weak_proper_sim_monotonicity_aux [mono]: "\<X> \<le> \<Y> \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><\<X>> q \<longrightarrow> p \<leadsto>\<^sub>\<sharp><\<Y>> q"
  using weak_proper_sim_monotonicity by simp

coinductive
  weak_proper_bisimilarity :: "process \<Rightarrow> process \<Rightarrow> bool" (infixr "\<approx>\<^sub>\<sharp>" 50)
where
  step: "\<lbrakk> p \<leadsto>\<^sub>\<sharp><(\<approx>\<^sub>\<sharp>)> q; q \<approx>\<^sub>\<sharp> p \<rbrakk> \<Longrightarrow> p \<approx>\<^sub>\<sharp> q"

(*** Primitive inference rules (coinduction, introduction and elimination) ***)

(**** Up-to techniques for the bisimilarity proof method. ****)

(* Bisimulation up-to (strong) bisimilarity. *)

lemma weak_proper_bisim_up_to_strong_bisim[consumes 1, case_names sim sym]:
  assumes "\<X> p q"
  and     "\<And>r s. \<X> r s \<Longrightarrow> r \<leadsto>\<^sub>\<sharp><((\<sim>\<^sub>\<sharp>) OO \<X> OO (\<sim>\<^sub>\<sharp>))> s"
  and     "\<And>r s. \<X> r s \<Longrightarrow> \<X> s r"
  shows   "p \<approx>\<^sub>\<sharp> q"
  using assms
proof -
  have "(\<sim>\<^sub>\<sharp>) OO \<X> OO (\<sim>\<^sub>\<sharp>) \<le> (\<approx>\<^sub>\<sharp>)" sorry (* TODO: Prove it. *)
  then show ?thesis
    using `\<X> p q` by blast
qed

(**** Basic bisimilarity proof method. *****)

lemma weak_proper_bisim_proof_method_aux[consumes 1, case_names weak_proper_bisim, case_conclusion weak_proper_bisim step]:
  assumes related: "\<X> p q"
  and     step:    "\<And>p q. \<X> p q \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><\<X>> q \<and> \<X> q p"
  shows            "p \<approx>\<^sub>\<sharp> q"
  using assms
proof (coinduct rule: weak_proper_bisimilarity.coinduct)
  case weak_proper_bisimilarity
  then show ?case
    by (smt step predicate2D predicate2I proper.lift_monotonicity)
qed

lemma weak_proper_bisim_proof_method[consumes 1, case_names sim sym]:
  assumes "\<X> p q"
  and     "\<And>p q. \<X> p q \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><\<X>> q"
  and     "\<And>p q. \<X> p q \<Longrightarrow> \<X> q p"
  shows   "p \<approx>\<^sub>\<sharp> q"
  using assms
by (coinduct rule: weak_proper_bisim_proof_method_aux) auto

lemma weak_proper_bisim_elim1: "p \<approx>\<^sub>\<sharp> q \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><(\<approx>\<^sub>\<sharp>)> q"
  by (auto dest: weak_proper_bisimilarity.cases)

lemma weak_proper_bisim_elim2: "p \<approx>\<^sub>\<sharp> q \<Longrightarrow> q \<approx>\<^sub>\<sharp> p"
  by (auto dest: weak_proper_bisimilarity.cases)

lemma weak_basic_bisim_intro: "\<lbrakk> p \<leadsto>\<^sub>\<sharp><(\<approx>\<^sub>\<sharp>)> q; q \<approx>\<^sub>\<sharp> p \<rbrakk> \<Longrightarrow> p \<approx>\<^sub>\<sharp> q"
  by (auto intro: weak_proper_bisimilarity.intros)

(*** Weak bisimilarity includes strong bisimilarity ***)

(* TODO: Prove it. *)
lemma strong_proper_sim_imp_weak_proper_sim: "p \<lesssim>\<^sub>\<sharp> q \<Longrightarrow> p \<leadsto>\<^sub>\<sharp><(\<approx>\<^sub>\<sharp>)> q"
  sorry

(* TODO: Prove it. *)
lemma strong_proper_bisim_imp_weak_proper_bisim: "p \<sim>\<^sub>\<sharp> q \<Longrightarrow> p \<approx>\<^sub>\<sharp> q"
  sorry

(*** Weak bisimilarity is an equivalence relation ***)

lemma weak_proper_bisim_reflexivity: "p \<approx>\<^sub>\<sharp> p"
proof -
  have "p = p" by simp
  then show ?thesis
    using weak_proper_bisim_proof_method_aux and weak_proper_sim_reflexivity by blast
qed

lemma weak_proper_bisim_symmetry [sym]: "p \<approx>\<^sub>\<sharp> q \<Longrightarrow> q \<approx>\<^sub>\<sharp> p"
  using weak_proper_bisim_elim2 by auto

lemma weak_proper_bisim_transitivity [trans]: "\<lbrakk> p \<approx>\<^sub>\<sharp> q; q \<approx>\<^sub>\<sharp> r \<rbrakk> \<Longrightarrow> p \<approx>\<^sub>\<sharp> r"
proof -
  assume "p \<approx>\<^sub>\<sharp> q" and "q \<approx>\<^sub>\<sharp> r"
  let ?\<X> = "(\<approx>\<^sub>\<sharp>) OO (\<approx>\<^sub>\<sharp>)"
  have "?\<X> p r" using \<open>p \<approx>\<^sub>\<sharp> q\<close> and \<open>q \<approx>\<^sub>\<sharp> r\<close> by blast
  then show ?thesis
  proof (coinduct rule: weak_proper_bisim_proof_method)
    case (sim p r)
    then obtain q where "p \<approx>\<^sub>\<sharp> q" and "q \<approx>\<^sub>\<sharp> r" using \<open>?\<X> p r\<close> by auto
    then have "q \<leadsto>\<^sub>\<sharp><(\<approx>\<^sub>\<sharp>)> r" using weak_proper_bisim_elim1 by auto
    moreover have "?\<X> \<le> ?\<X>" by simp
    ultimately show ?case using weak_proper_bisim_elim1 and weak_proper_sim_transitivity and \<open>p \<approx>\<^sub>\<sharp> q\<close> by blast
  next
    case (sym p r)
    then show ?case using weak_proper_bisim_symmetry by auto
  qed
qed

(*** Preservation laws ***)
(* TODO: Prove them. *)

lemma weak_proper_receive_preservation: "(\<And>x. P x \<approx>\<^sub>\<sharp> Q x) \<Longrightarrow> m \<triangleright> x. P x \<approx>\<^sub>\<sharp> m \<triangleright> x. Q x" sorry
lemma weak_proper_parallel_preservation:
  assumes "p \<approx>\<^sub>\<sharp> q"
  shows "p \<parallel> r \<approx>\<^sub>\<sharp> q \<parallel> r" and "r \<parallel> p \<approx>\<^sub>\<sharp> r \<parallel> q"
  sorry
lemma weak_proper_new_channel_preservation: "(\<And>a. P a \<approx>\<^sub>\<sharp> Q a) \<Longrightarrow> \<nu> a. P a \<approx>\<^sub>\<sharp> \<nu> a. Q a" sorry

(*** Structural congruence laws ***)

lemma weak_proper_receive_scope_extension: "a \<triangleright> x. \<nu> b. P x b \<approx>\<^sub>\<sharp> \<nu> b. a \<triangleright> x. P x b"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_receive_scope_extension by simp

lemma weak_proper_parallel_scope_extension: "\<nu> a. P a \<parallel> q \<approx>\<^sub>\<sharp> \<nu> a. (P a \<parallel> q)"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_parallel_scope_extension by simp

lemma weak_proper_new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<approx>\<^sub>\<sharp> \<nu> a. \<nu> b. P a b"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_new_channel_scope_extension by simp

lemma weak_proper_parallel_unit: "\<zero> \<parallel> p \<approx>\<^sub>\<sharp> p"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_parallel_unit by simp

lemma weak_proper_parallel_associativity: "(p \<parallel> q) \<parallel> r \<approx>\<^sub>\<sharp> p \<parallel> (q \<parallel> r)"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_parallel_associativity by simp

lemma weak_proper_parallel_commutativity: "p \<parallel> q \<approx>\<^sub>\<sharp> q \<parallel> p"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_parallel_commutativity by simp

lemma weak_proper_scope_redundancy: "p \<approx>\<^sub>\<sharp> \<nu> a. p"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_scope_redundancy by simp

end
