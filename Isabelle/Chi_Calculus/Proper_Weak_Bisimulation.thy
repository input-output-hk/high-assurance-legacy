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

lemma "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q"
  (* TODO: Find a better proof. *)
  using proper_transition.simple weak_tau_respecting_basic_transition_acting_elim weak_tau_respecting_proper_transition_simple_intro by blast

lemma "P \<Longrightarrow>\<^sub>\<flat>\<lbrace>c \<triangleleft> V\<rbrace> Q \<Longrightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q"
  (* TODO: Find a better proof. *)
  using output_without_opening weak_tau_respecting_basic_transition_acting_elim weak_tau_respecting_proper_transition_output_without_opening_intro by blast

(** Weak proper transition \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ **)

definition weak_proper_transition :: "process \<Rightarrow> proper_residual \<Rightarrow> bool"
  (infix "\<Longrightarrow>\<^sub>\<sharp>\<^sup>^" 50)
  where
   "P \<Longrightarrow>\<^sub>\<sharp>\<^sup>^C \<equiv>
      case C of
        \<lparr>\<delta>\<rparr> Q \<Rightarrow> P \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q \<or> (\<delta> = \<tau> \<and> P = Q) |
        \<lparr>c \<triangleleft> V\<rparr> Q \<Rightarrow> P = Q |
        Output c \<K> \<Rightarrow> P \<Longrightarrow>\<^sub>\<sharp> Output c \<K>"

end
