theory Proper_Weak_Bisimulation
  imports Typed_Proper_Transition_System Basic_Weak_Bisimulation
begin

lemma proper_tau_trans_is_basic_tau_trans: "(P \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> Q) = (P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q)"
  by (metis basic_action_of.simps(2) proper_residual.distinct(1) proper_residual.inject(1) proper_transition.simps)

(* TODO: Rename \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> to \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> in `Basic_Weak_Bisimulation`, then remove the following abbreviation. *)
abbreviation
  proper_tau_sequence :: "process \<Rightarrow> process \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sup>\<tau>" 50)
where
  "op \<Longrightarrow>\<^sup>\<tau> \<equiv> op \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat>"

(* Weak Semantics *)

(** Weak \<tau>-respecting proper transition \<Longrightarrow>\<^sub>\<sharp>C **)

inductive
  weak_tau_respecting_proper_transition :: "process \<Rightarrow> proper_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<sharp>" 50)
where
  simple:
    "\<exists>R S. P \<Longrightarrow>\<^sup>\<tau> R \<and> R \<longmapsto>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> S \<and> S \<Longrightarrow>\<^sup>\<tau> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" |
  output_without_opening:
    "\<exists>R S. P \<Longrightarrow>\<^sup>\<tau> R \<and> R \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> S \<and> S \<Longrightarrow>\<^sup>\<tau> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q" |
  output_with_opening:
    "\<exists>\<Q>. P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<and> (\<forall>a. \<Q> a \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<K> a) \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a"

(*** NOTE: \<tau>-prefix simulation, just to be used in examples. ***)
abbreviation
  tau_prefix :: "process \<Rightarrow> process"
where
  "tau_prefix P \<equiv> \<nu> x. (x \<triangleleft> undefined \<parallel> x \<triangleright> _. P)"

syntax
  "_tau_prefix" :: "process \<Rightarrow> process" ("(3\<tau>./ _)" [100] 100)
translations
  "\<tau>. P" \<rightleftharpoons> "CONST tau_prefix P"

lemma tau_prefix_transition: "\<tau>. P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> x. (\<zero> \<parallel> P)"
proof -
  have A: "\<tau>. P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> x\<rbrace> x \<triangleleft> undefined \<parallel> x \<triangleright> _. P"
    using opening by simp
  moreover have "\<And>x. x \<triangleleft> undefined \<longmapsto>\<^sub>\<flat>\<lbrace>x \<triangleleft> undefined\<rbrace> \<zero>"
    using sending by simp
  moreover have "\<And>x. x \<triangleright> _. P \<longmapsto>\<^sub>\<flat>\<lbrace>x \<triangleright> undefined\<rbrace> P"
    using receiving by blast
  ultimately have "\<And>x. x \<triangleleft> undefined \<parallel> x \<triangleright> _. P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> P"
    using communication ltr by blast
  then show ?thesis using scoped_acting and A by simp
qed

lemma "\<nu>\<degree> x. c \<triangleleft>\<degree> x \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree> x\<rbrace> c \<triangleleft>\<degree> x"
  by (simp add: weak_tau_respecting_basic_transition_opening)

lemma "\<And>x. c \<triangleleft>\<degree> x \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft>\<degree> x\<rparr> \<zero>"
  using
    proper_transition.output_without_opening and
    typed_sending and
    weak_tau_respecting_proper_transition.output_without_opening
  by fastforce

lemma "\<And>x. c \<triangleleft> x \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> x\<rparr> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
proof -
  have "\<And>x. c \<triangleleft> x \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sup>\<tau> c \<triangleleft> x \<parallel> \<tau>. \<zero>"
    by simp
  moreover have "\<And>x. c \<triangleleft> x \<parallel> \<tau>. \<zero> \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> x\<rparr> \<zero> \<parallel> \<tau>. \<zero>"
  proof -
    have "\<And>x. c \<triangleleft> x \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft> x\<rbrace> \<zero>"
      using sending by simp
    then have "\<And>x. c \<triangleleft> x \<parallel> \<tau>. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft> x\<rbrace> \<zero> \<parallel> \<tau>. \<zero>"
      using acting_left by simp
    then show "\<And>x. c \<triangleleft> x \<parallel> \<tau>. \<zero> \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> x\<rparr> \<zero> \<parallel> \<tau>. \<zero>"
      using proper_transition.output_without_opening by simp
  qed
  moreover have "\<zero> \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sup>\<tau> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
  proof -
    have "\<tau>. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> z. (\<zero> \<parallel> \<zero>)"
      using tau_prefix_transition by simp
    then have "\<zero> \<parallel> \<tau>. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
      using acting_right by simp
    then show "\<zero> \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sup>\<tau> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
      using tau_transition_is_tau_sequence by simp
  qed
  ultimately show "\<And>x. c \<triangleleft> x \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> x\<rparr> \<zero> \<parallel> \<nu> z. (\<zero> \<parallel> \<zero>)"
    using weak_tau_respecting_proper_transition.output_without_opening by fastforce
qed

(* TODO: Prove it. *)
lemma "\<nu>\<degree> x. c \<triangleleft>\<degree> x \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft>\<degree> \<nu>\<degree> x. x\<rparr> \<zero> \<parallel> \<nu>\<degree> z. (\<zero> \<parallel> \<zero>)" sorry

(* TODO: Prove it. *)
lemma lem5: "\<nu>\<degree> x y. c \<triangleleft>\<degree> (x, y) \<parallel> \<tau>. \<zero> \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft>\<degree> \<nu>\<degree> x y. (x, y)\<rparr> \<zero> \<parallel> \<nu>\<degree> z. (\<zero> \<parallel> \<zero>)" sorry

(*** Intro rules ***)

lemma weak_tau_respecting_proper_transition_simple_intro: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau> R; R \<longmapsto>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> S; S \<Longrightarrow>\<^sup>\<tau> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q"
  using weak_tau_respecting_proper_transition.simple by fastforce

lemma weak_tau_respecting_proper_transition_output_without_opening_intro: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau> R; R \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> S; S \<Longrightarrow>\<^sup>\<tau> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q"
  using weak_tau_respecting_proper_transition.output_without_opening by fastforce

lemma weak_tau_respecting_proper_transition_output_with_opening_intro: "\<lbrakk> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Q> a \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<K> a \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a"
  using weak_tau_respecting_proper_transition.output_with_opening by fastforce

(*** Elim rules ***)

lemma weak_tau_respecting_proper_transition_simple_elim: "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<Longrightarrow> \<exists>R S. P \<Longrightarrow>\<^sup>\<tau> R \<and> R \<longmapsto>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> S \<and> S \<Longrightarrow>\<^sup>\<tau> Q"
proof (induction P "\<lparr>\<delta>\<rparr> Q" rule: weak_tau_respecting_proper_transition.induct)
  case simple
  then show ?case by simp
qed

lemma weak_tau_respecting_proper_transition_output_without_opening_elim: "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q \<Longrightarrow> \<exists>R S. P \<Longrightarrow>\<^sup>\<tau> R \<and> R \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> S \<and> S \<Longrightarrow>\<^sup>\<tau> Q"
proof (induction P "\<lparr>c \<triangleleft> V\<rparr> Q" rule: weak_tau_respecting_proper_transition.induct)
  case output_without_opening
  then show ?case by simp
qed

lemma weak_tau_respecting_proper_transition_output_with_opening_elim: "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a \<Longrightarrow> \<exists>\<Q>. P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<and> (\<forall>a. \<Q> a \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<K> a)"
proof (induction P "\<lparr>c \<triangleleft> \<nu> a. \<K> a" arbitrary: \<K> rule: weak_tau_respecting_proper_transition.induct)
  case output_with_opening
  then show ?case by auto
qed

(*** Strong to weak transitions ***)

lemma weak_tau_respecting_proper_transition_single_simple: "P \<longmapsto>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q"
  using weak_tau_respecting_proper_transition_simple_intro by blast

lemma weak_tau_respecting_proper_transition_single_output_without_opening: "P \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q"
  using weak_tau_respecting_proper_transition_output_without_opening_intro by blast

lemma weak_tau_respecting_proper_transition_single_output_with_opening: "P \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a"
proof (induction P "\<lparr>c \<triangleleft> \<nu> a. \<K> a" arbitrary: \<K> rule: proper_transition.induct)
  case (output_with_opening P \<Q> \<K>)
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

lemma weak_tau_respecting_proper_transition_tau: "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> Q \<Longrightarrow> P \<Longrightarrow>\<^sup>\<tau> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> Q"
  then obtain R and S where "P \<Longrightarrow>\<^sup>\<tau> R" and "R \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> S" and "S \<Longrightarrow>\<^sup>\<tau> Q"
    using weak_tau_respecting_proper_transition_simple_elim by fastforce
  then have "R \<Longrightarrow>\<^sup>\<tau> S" using \<open>R \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> S\<close> and tau_transition_is_tau_sequence and proper_tau_trans_is_basic_tau_trans by simp
  then show ?thesis using \<open>P \<Longrightarrow>\<^sup>\<tau> R\<close> and \<open>S \<Longrightarrow>\<^sup>\<tau> Q\<close> by (simp add: tau_sequence_trans)
qed

lemma prepend_tau_sequence_to_weak_tau_respecting_proper_transition_simple: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau> R; R \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q"
  (* TODO: Find a better proof (see `prepend_tau_sequence_to_weak_tau_respecting_basic_transition_acting`) *)
  by (metis (no_types, lifting) tau_sequence_trans weak_tau_respecting_proper_transition_simple_elim weak_tau_respecting_proper_transition_simple_intro)

lemma prepend_tau_sequence_to_weak_tau_respecting_proper_transition_output_without_opening: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau> R; R \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q"
  (* TODO: Find a better proof. *)
  by (smt rtrancl_trans weak_tau_respecting_proper_transition.output_without_opening weak_tau_respecting_proper_transition_output_without_opening_elim)

lemma prepend_tau_sequence_to_weak_tau_respecting_proper_transition_output_with_opening: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau> R; R \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a"
  (* TODO: Find a better proof. *)
  by (metis (no_types, lifting) prepend_tau_sequence_to_weak_tau_respecting_basic_transition_opening weak_tau_respecting_proper_transition.output_with_opening weak_tau_respecting_proper_transition_output_with_opening_elim)

lemma append_tau_sequence_to_weak_tau_respecting_proper_transition_simple: "\<lbrakk> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> R; R \<Longrightarrow>\<^sup>\<tau> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q"
  (* TODO: Find a better proof (see `append_tau_sequence_to_weak_tau_respecting_basic_transition_acting`) *)
  by (metis (no_types, lifting) converse_rtrancl_into_rtrancl rtrancl_idemp weak_tau_respecting_proper_transition.simple weak_tau_respecting_proper_transition_simple_elim)

lemma append_tau_sequence_to_weak_tau_respecting_proper_transition_output_without_opening: "\<lbrakk> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> R; R \<Longrightarrow>\<^sup>\<tau> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q"
  (* TODO: Find a better proof. *)
  by (metis (no_types, lifting) tau_sequence_trans weak_tau_respecting_proper_transition_output_without_opening_elim weak_tau_respecting_proper_transition_output_without_opening_intro)

(* NOTE: Check that a lemma like the following lemma makes some sense.
lemma append_tau_sequence_to_weak_tau_respecting_proper_transition_output_with_opening: "\<lbrakk> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a; ? \<Longrightarrow>\<^sup>\<tau> Q \<rbrakk> \<Longrightarrow> ?"
*)

(** Lifted weak \<tau>-respecting proper operational semantics **)

lemma weak_tau_respecting_proper_transition_simple: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q"
  (* TODO: Find a better proof. *)
  using proper_transition.simple weak_tau_respecting_basic_transition_acting_elim weak_tau_respecting_proper_transition_simple_intro by blast

lemma weak_tau_respecting_proper_transition_output_without_opening: "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>c \<triangleleft> V\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q"
  (* TODO: Find a better proof. *)
  using output_without_opening weak_tau_respecting_basic_transition_acting_elim weak_tau_respecting_proper_transition_output_without_opening_intro by blast

(** Weak proper transition \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ **)

definition weak_proper_transition :: "process \<Rightarrow> proper_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<sharp>\<^sup>^" 50)
  where
   "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^C \<equiv>
      case C of
        \<lparr>\<delta>\<rparr> Q \<Rightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<or> (\<delta> = \<tau> \<and> P = Q) |
        \<lparr>c \<triangleleft> V\<rparr> Q \<Rightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q |
        Output c \<K> \<Rightarrow> P \<Longrightarrow>\<^sub>\<sharp> Output c \<K>"

lemma prepend_tau_transition_to_weak_proper_transition: "\<lbrakk> P \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> R; R \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
proof -
  assume "P \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> R" and "R \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
  then have "R \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<or> \<delta> = \<tau> \<and> R = Q"
    by (simp add: weak_proper_transition_def)
  then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<or> \<delta> = \<tau> \<and> P = Q"
    using
      \<open>P \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> R\<close> and
      prepend_tau_sequence_to_weak_tau_respecting_proper_transition_simple and
      weak_tau_respecting_proper_transition_single_simple and
      weak_tau_respecting_proper_transition_tau
    by meson
  then show ?thesis
    by (simp add: weak_proper_transition_def)
qed

lemma append_tau_transition_to_weak_proper_transition: "\<lbrakk> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> R; R \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> R" and "R \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> Q"
  then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> R \<or> \<delta> = \<tau> \<and> P = R"
    by (simp add: weak_proper_transition_def)
  then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<or> \<delta> = \<tau> \<and> P = Q"
    using
      \<open>R \<longmapsto>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> Q\<close> and
      append_tau_sequence_to_weak_tau_respecting_proper_transition_simple and
      weak_tau_respecting_proper_transition_single_simple and
      weak_tau_respecting_proper_transition_tau
    by meson
  then show ?thesis
    by (simp add: weak_proper_transition_def)
qed

lemma tau_sequence_is_weak_proper_tau_transition: "P \<Longrightarrow>\<^sup>\<tau> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by (simp add: weak_proper_transition_def)
next
  case (tau_seq_step R S)
  then show ?case
    using append_tau_transition_to_weak_proper_transition and proper_transition.simple by auto
qed

lemma weak_proper_tau_transition_is_tau_sequence: "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> Q \<Longrightarrow> P \<Longrightarrow>\<^sup>\<tau> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> Q"
  then show ?thesis
  proof (cases "P = Q")
    case True
    then show ?thesis by (simp add: tau_sequence_refl)
  next
    case False
    then have " P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> Q" using \<open>P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> Q\<close> and weak_proper_transition_def by force
    then show ?thesis using weak_tau_respecting_proper_transition_tau by fastforce
  qed
qed

lemma weak_proper_transition_refl_intro: "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> P"
  by (simp add: weak_proper_transition_def)

lemma weak_proper_transition_step_intro: "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
  by (simp add: weak_proper_transition_def)

lemma weak_proper_transition_step_elim: "\<lbrakk> P \<noteq> Q; P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q"
  by (simp add: weak_proper_transition_def)

lemma weak_proper_transition_induction
  [consumes 1, case_names weak_proper_tran_refl weak_proper_tran_step]:
  assumes "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
  and     "\<PP> ProperSilent P"
  and     "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<Longrightarrow> \<PP> \<delta> Q"
  shows   "\<PP> \<delta> Q"
  using assms
  by (auto simp add: weak_proper_transition_def)

lemma weak_proper_transition_single_simple: "P \<longmapsto>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
  using weak_tau_respecting_proper_transition_simple_intro and weak_proper_transition_step_intro by fastforce

lemma prepend_tau_sequence_to_weak_proper_transition: "\<lbrakk> P \<Longrightarrow>\<^sup>\<tau> R; R \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
proof -
  assume "P \<Longrightarrow>\<^sup>\<tau> R" and "R \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
  then show ?thesis
  proof (cases "R = Q")
    case True
    then have A1: "P \<Longrightarrow>\<^sup>\<tau> Q" using \<open>P \<Longrightarrow>\<^sup>\<tau> R\<close> and True by simp
    moreover have A2: "Q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q" using \<open>R \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<delta> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_proper_tau_transition)
    next
      case False
      then have "Q \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" using A2 and False by (simp add: weak_proper_transition_def)
      then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" using A1 by (simp add: prepend_tau_sequence_to_weak_tau_respecting_proper_transition_simple)
      then show ?thesis by (simp add: weak_proper_transition_step_intro)
    qed
  next
    case False
    then have "R \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" using \<open>R \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q\<close> by (simp add: weak_proper_transition_step_elim)
    then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" using \<open>P \<Longrightarrow>\<^sup>\<tau> R\<close> and prepend_tau_sequence_to_weak_tau_respecting_proper_transition_simple by simp
    then show ?thesis by (simp add: weak_proper_transition_step_intro)
  qed
qed

lemma append_tau_sequence_to_weak_proper_transition: "\<lbrakk> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> R; R \<Longrightarrow>\<^sup>\<tau> Q \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
proof -
  assume "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> R" and "R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  then show ?thesis
  proof (cases "P = R")
    case True
    then have A1: "P \<Longrightarrow>\<^sup>\<tau> Q" using \<open>R \<Longrightarrow>\<^sup>\<tau> Q\<close> and True by simp
    moreover have A2: "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> P" using \<open>P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> R\<close> and True by simp
    ultimately show ?thesis
    proof (cases "\<delta> = \<tau>")
      case True
      then show ?thesis using A1 and A2 and True by (simp add: tau_sequence_is_weak_proper_tau_transition)
    next
      case False
      then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> P" using A2 and False by (simp add: weak_proper_transition_def)
      then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" using A1 by (simp add: append_tau_sequence_to_weak_tau_respecting_proper_transition_simple)
      then show ?thesis by (simp add: weak_proper_transition_step_intro)
    qed
  next
    case False
    then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> R" using \<open>P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> R\<close> by (simp add: weak_proper_transition_step_elim)
    then have "P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" using \<open>R \<Longrightarrow>\<^sup>\<tau> Q\<close> and append_tau_sequence_to_weak_tau_respecting_proper_transition_simple by simp
    then show ?thesis by (simp add: weak_proper_transition_step_intro)
  qed
qed

(** Lifted weak proper operational semantics **)

lemma weak_proper_transition_simple: "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>basic_action_of \<delta>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> Q"
  (* TODO: Find a nicer proof. *)
  by (smt basic_action.distinct(1) basic_action_of.simps(1) basic_residual.simps(5) proper_action.exhaust proper_residual.simps(5) weak_basic_transition_def weak_proper_transition_def weak_tau_respecting_proper_transition_simple) 

lemma weak_proper_transition_output_without_opening: "P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>c \<triangleleft> V\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>c \<triangleleft> V\<rparr> Q"
  by (simp add: weak_basic_transition_def weak_proper_transition_def weak_tau_respecting_proper_transition_output_without_opening)

lemma weak_proper_transition_output_with_opening: "\<lbrakk> P \<Longrightarrow>\<^sub>\<flat>\<^sup>^\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Q> a \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>c \<triangleleft> \<K> a \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>c \<triangleleft> \<nu> a. \<K> a"
  (* TODO: Find a nicer proof. *)
  by (smt basic_residual.simps(6) output_rest.exhaust output_rest.simps(5) output_rest.simps(6) proper_residual.simps(6) weak_basic_transition_def weak_proper_transition_def weak_tau_respecting_proper_transition.output_with_opening)

(** Misc proofs **)

lemma weak_proper_transition_sending: "c \<triangleleft> V \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>c \<triangleleft> V\<rparr> \<zero>"
proof -
  have "c \<triangleleft> V \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> \<zero>"
  proof -
    have "c \<triangleleft> V \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft> V\<rbrace> \<zero>" using sending by simp
    then have "c \<triangleleft> V \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> \<zero>" using proper_transition.output_without_opening by simp
    then show ?thesis using weak_tau_respecting_proper_transition_single_output_without_opening by simp
  qed
  then show ?thesis  by (simp add: weak_proper_transition_def)
qed

(* Weak proper bisimilarity *)

(** Weak proper simulation **)

abbreviation
  weak_proper_simulation :: "process \<Rightarrow> (process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> process \<Rightarrow> bool"
  ("_ \<leadsto>\<^sub>\<sharp><_> _" [50, 50, 50] 50)
where
  "P \<leadsto>\<^sub>\<sharp><\<X>> Q \<equiv> \<forall>C. P \<longmapsto>\<^sub>\<sharp>C \<longrightarrow> (\<exists>D. Q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^D \<and> proper_lift \<X> C D)"

abbreviation
  is_weak_proper_sim
where
  "is_weak_proper_sim \<X> \<equiv> \<forall>P Q. \<X> P Q \<longrightarrow> P \<leadsto>\<^sub>\<sharp><\<X>> Q"

lemma weak_proper_sim_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><\<X>> Q \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><\<Y>> Q"
  by (meson predicate2D proper_lift_monotonicity)

(*** Introduction and elimination rules. ***)

(* TODO: Is this needed? *)
lemma weak_proper_sim_intro: "(\<And>C. P \<longmapsto>\<^sub>\<sharp>C \<and> (\<exists>D. Q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^D \<and> proper_lift \<X> C D)) \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><\<X>> Q"
  by simp

(* TODO: Is this needed? *)
lemma weak_proper_sim_elim: "\<lbrakk> P \<leadsto>\<^sub>\<sharp><\<X>> Q; P \<longmapsto>\<^sub>\<sharp>C \<rbrakk> \<Longrightarrow> \<exists>D. Q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^D \<and> proper_lift \<X> C D"
  by simp

(*** Simulation is a pre-order relation. ***)

(* TODO: Prove it. *)
lemma weak_proper_sim_reflexivity: "(\<And>P. \<X> P P) \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><\<X>> P" sorry

(* TODO: Prove it. *)
lemma weak_proper_sim_transitivity:
  assumes A\<^sub>1: "Q \<leadsto>\<^sub>\<sharp><\<Y>> R"
  and     A\<^sub>2: "\<X> OO \<Y> \<le> \<Z>"
  and     A\<^sub>3: "is_weak_proper_sim \<X>"
  and     A\<^sub>4: "\<X> P Q"
  shows "P \<leadsto>\<^sub>\<sharp><\<Z>> R"
  sorry

(*** Preservation laws for simulation. ***)

(* TODO: Prove it. *)
lemma pre_weak_proper_receive_preservation: "(\<And>x. \<X> (\<P> x) (\<Q> x)) \<Longrightarrow> c \<triangleright>\<degree> x. \<P> x \<leadsto>\<^sub>\<sharp><\<X>> c \<triangleright>\<degree> x. \<Q> x" sorry

(* TODO: Prove it. *)
lemma pre_left_weak_proper_parallel_preservation:
  assumes "P \<leadsto>\<^sub>\<sharp><\<X>> Q"
  and     "\<X> P Q"
  and     "\<And>S T U. \<X> S T \<Longrightarrow> \<Y> (U \<parallel> S) (U \<parallel> T)"
  and     "\<And>\<S> \<T>. (\<And>x. \<Y> (\<S> x) (\<T> x)) \<Longrightarrow> \<Y> (NewChannel \<S>) (NewChannel \<T>)"
  shows   "R \<parallel> P \<leadsto>\<^sub>\<sharp><\<Y>> R \<parallel> Q"
  sorry

(* TODO: Prove it. *)
lemma pre_weak_proper_new_channel_preservation:
  assumes "\<And>x. \<P> x \<leadsto>\<^sub>\<sharp><\<X>> \<Q> x"
  and     "\<And>\<R> \<S> y. (\<And>x. \<X> (\<R> x) (\<S> x)) \<Longrightarrow> \<Y> (NewChannel \<R>) (NewChannel \<S>)"
  and     "\<X> \<le> \<Y>"
  shows   "NewChannel \<P> \<leadsto>\<^sub>\<sharp><\<Y>> NewChannel \<Q>"
  sorry

(** Weak proper bisimulation **)

lemma weak_proper_sim_monotonicity_aux: "\<X> \<le> \<Y> \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><\<X>> Q \<longrightarrow> P \<leadsto>\<^sub>\<sharp><\<Y>> Q"
  using weak_proper_sim_monotonicity by simp

coinductive
  weak_proper_bisimilarity :: "process \<Rightarrow> process \<Rightarrow> bool" (infixr "\<approx>\<^sub>\<sharp>" 50)
where
  step: "\<lbrakk> P \<leadsto>\<^sub>\<sharp><op \<approx>\<^sub>\<sharp>> Q; Q \<approx>\<^sub>\<sharp> P \<rbrakk> \<Longrightarrow> P \<approx>\<^sub>\<sharp> Q"
monos weak_proper_sim_monotonicity_aux

(*** Primitive inference rules (coinduction, introduction and elimination) ***)

lemma weak_proper_bisim_coinduct_aux[consumes 1, case_names weak_proper_bisim, case_conclusion weak_proper_bisim step]:
  assumes related: "\<X> P Q"
  and     step:    "\<And>P Q. \<X> P Q \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><(\<X> \<squnion> op \<approx>\<^sub>\<sharp>)> Q \<and> (\<X> \<squnion> op \<approx>\<^sub>\<sharp>) Q P"
  shows            "P \<approx>\<^sub>\<sharp> Q"
proof -
  have aux: "\<X> \<squnion> op \<approx>\<^sub>\<sharp> = (\<lambda>P Q. \<X> P Q \<or> P \<approx>\<^sub>\<sharp> Q)" by blast
  show ?thesis using related
    by (coinduct, force dest: step simp add: aux)
qed

lemma weak_proper_bisim_weak_coinduct_aux[consumes 1, case_names weak_proper_bisim, case_conclusion weak_proper_bisim step]:
  assumes related: "\<X> P Q"
  and     step:    "\<And>P Q. \<X> P Q \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><\<X>> Q \<and> \<X> Q P"
  shows            "P \<approx>\<^sub>\<sharp> Q"
  using related
proof (coinduct rule: weak_proper_bisim_coinduct_aux)
  case (weak_proper_bisim P Q)
  from step[OF this] show ?case using weak_proper_sim_monotonicity by blast
qed

lemma weak_proper_bisim_coinduct[consumes 1, case_names sim sym]:
  assumes "\<X> P Q"
  and     "\<And>R S. \<X> R S \<Longrightarrow> R \<leadsto>\<^sub>\<sharp><(\<X> \<squnion> op \<approx>\<^sub>\<sharp>)> S"
  and     "\<And>R S. \<X> R S \<Longrightarrow> \<X> S R"
  shows   "P \<approx>\<^sub>\<sharp> Q"
  using assms
by (coinduct rule: weak_proper_bisim_coinduct_aux) auto

lemma weak_proper_bisim_weak_coinduct[consumes 1, case_names sim sym]:
  assumes "\<X> P Q"
  and     "\<And>P Q. \<X> P Q \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><\<X>> Q"
  and     "\<And>P Q. \<X> P Q \<Longrightarrow> \<X> Q P"
  shows   "P \<approx>\<^sub>\<sharp> Q"
  using assms
by (coinduct rule: weak_proper_bisim_weak_coinduct_aux) auto

lemma weak_proper_bisim_elim1: "P \<approx>\<^sub>\<sharp> Q \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><op \<approx>\<^sub>\<sharp>> Q"
  by (auto dest: weak_proper_bisimilarity.cases)

lemma weak_proper_bisim_elim2: "P \<approx>\<^sub>\<sharp> Q \<Longrightarrow> Q \<approx>\<^sub>\<sharp> P"
  by (auto dest: weak_proper_bisimilarity.cases)

lemma weak_basic_bisim_intro: "\<lbrakk> P \<leadsto>\<^sub>\<sharp><op \<approx>\<^sub>\<sharp>> Q; Q \<approx>\<^sub>\<sharp> P \<rbrakk> \<Longrightarrow> P \<approx>\<^sub>\<sharp> Q"
  by (auto intro: weak_proper_bisimilarity.intros)

(*** Weak bisimilarity includes strong bisimilarity ***)

(* TODO: Prove it. *)
lemma strong_proper_sim_imp_weak_proper_sim: "P \<preceq>\<^sub>\<sharp> Q \<Longrightarrow> P \<leadsto>\<^sub>\<sharp><\<X>> Q"
  sorry

(* TODO: Prove it. *)
lemma strong_proper_bisim_imp_weak_proper_bisim: "P \<sim>\<^sub>\<sharp> Q \<Longrightarrow> P \<approx>\<^sub>\<sharp> Q"
  sorry

(*** Weak bisimilarity is an equivalence relation ***)

lemma weak_proper_bisim_reflexivity: "P \<approx>\<^sub>\<sharp> P"
proof -
  have "P = P" by simp
  then show ?thesis
    using weak_proper_bisim_weak_coinduct_aux and weak_proper_sim_reflexivity by blast
qed

lemma weak_proper_bisim_symmetry: "P \<approx>\<^sub>\<sharp> Q \<Longrightarrow> Q \<approx>\<^sub>\<sharp> P"
  using weak_proper_bisim_elim2 by auto

lemma weak_proper_bisim_transitivity: "\<lbrakk> P \<approx>\<^sub>\<sharp> Q; Q \<approx>\<^sub>\<sharp> R \<rbrakk> \<Longrightarrow> P \<approx>\<^sub>\<sharp> R"
proof -
  assume "P \<approx>\<^sub>\<sharp> Q" and "Q \<approx>\<^sub>\<sharp> R"
  let ?\<X> = "op \<approx>\<^sub>\<sharp> OO op \<approx>\<^sub>\<sharp>"
  have "?\<X> P R" using \<open>P \<approx>\<^sub>\<sharp> Q\<close> and \<open>Q \<approx>\<^sub>\<sharp> R\<close> by blast
  then show ?thesis
  proof (coinduct rule: weak_proper_bisim_weak_coinduct)
    case (sim P R)
    then obtain Q where "P \<approx>\<^sub>\<sharp> Q" and "Q \<approx>\<^sub>\<sharp> R" using \<open>?\<X> P R\<close> by auto
    then have "Q \<leadsto>\<^sub>\<sharp><op \<approx>\<^sub>\<sharp>> R" using weak_proper_bisim_elim1 by auto
    moreover have "?\<X> \<le> ?\<X>" by simp
    ultimately show ?case using weak_proper_bisim_elim1 and weak_proper_sim_transitivity and \<open>P \<approx>\<^sub>\<sharp> Q\<close> by blast
  next
    case (sym P R)
    then show ?case using weak_proper_bisim_symmetry by auto
  qed
qed

(*** Preservation laws ***)
(* TODO: Prove them. *)

lemma weak_proper_receive_preservation: "(\<And>x. \<P> x \<approx>\<^sub>\<sharp> \<Q> x) \<Longrightarrow> m \<triangleright> x. \<P> x \<approx>\<^sub>\<sharp> m \<triangleright> x. \<Q> x" sorry
lemma weak_proper_parallel_preservation: "P \<approx>\<^sub>\<sharp> Q \<Longrightarrow> P \<parallel> R \<approx>\<^sub>\<sharp> Q \<parallel> R" sorry
lemma weak_proper_new_channel_preservation: "(\<And>a. \<P> a \<approx>\<^sub>\<sharp> \<Q> a) \<Longrightarrow> \<nu> a. \<P> a \<approx>\<^sub>\<sharp> \<nu> a. \<Q> a" sorry

(*** Structural congruence laws ***)

lemma weak_proper_receive_scope_extension: "c \<triangleright> x. \<nu> a. \<P> x a \<approx>\<^sub>\<sharp> \<nu> a. c \<triangleright> x. \<P> x a"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_receive_scope_extension by simp

lemma weak_proper_parallel_scope_extension: "\<nu> a. \<P> a \<parallel> Q \<approx>\<^sub>\<sharp> \<nu> a. (\<P> a \<parallel> Q)"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_parallel_scope_extension by simp

lemma weak_proper_new_channel_scope_extension: "\<nu> b. \<nu> a. \<P> a b \<approx>\<^sub>\<sharp> \<nu> a. \<nu> b. \<P> a b"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_new_channel_scope_extension by simp

lemma weak_proper_parallel_unit: "\<zero> \<parallel> P \<approx>\<^sub>\<sharp> P"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_parallel_unit by simp

lemma weak_proper_parallel_associativity: "(P \<parallel> Q) \<parallel> R \<approx>\<^sub>\<sharp> P \<parallel> (Q \<parallel> R)"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_parallel_associativity by simp

lemma weak_proper_parallel_commutativity: "P \<parallel> Q \<approx>\<^sub>\<sharp> Q \<parallel> P"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_parallel_commutativity by simp

lemma weak_proper_scope_redundancy: "P \<approx>\<^sub>\<sharp> \<nu> a. P"
  using strong_proper_bisim_imp_weak_proper_bisim and proper_scope_redundancy by simp


end

