section \<open>Transition Systems\<close>

theory Transition_Systems
  imports Main "HOL-Library.Lattice_Syntax" "HOL-Eisbach.Eisbach"
begin

locale residual =
  fixes lift :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> ('residual \<Rightarrow> 'residual \<Rightarrow> bool)"
  assumes lift_monotonicity:
    "\<X> \<le> \<Y> \<Longrightarrow> lift \<X> \<le> lift \<Y>"
  assumes lift_equality_preservation:
    "lift op = = op ="
  assumes lift_composition_preservation:
    "lift (\<X> OO \<Y>) = lift \<X> OO lift \<Y>"
  assumes lift_conversion_preservation:
    "lift \<X>\<inverse>\<inverse> = (lift \<X>)\<inverse>\<inverse>"
begin

lemma lift_weak_infimum_preservation: "lift (\<X> \<sqinter> \<Y>) \<le> lift \<X> \<sqinter> lift \<Y>"
  by (simp add: lift_monotonicity)

lemma lift_reverse_weak_supremum_preservation: "lift (\<X> \<squnion> \<Y>) \<ge> lift \<X> \<squnion> lift \<Y>"
  by (simp add: lift_monotonicity)

lemma lift_reflexivity_propagation: "reflp \<X> \<Longrightarrow> reflp (lift \<X>)"
  using reflp_eq and lift_monotonicity and lift_equality_preservation
  by metis

lemma lift_transitivity_propagation: "transp \<X> \<Longrightarrow> transp (lift \<X>)"
  using transp_relcompp and lift_monotonicity and lift_composition_preservation
  by metis

lemma lift_symmetry_propagation: "symp \<X> \<Longrightarrow> symp (lift \<X>)"
  using symp_conversep and lift_monotonicity and lift_conversion_preservation
  by metis

end

locale transition_system =
  residual lift for lift :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> ('residual \<Rightarrow> 'residual \<Rightarrow> bool)" +
  fixes transition :: "'context \<Rightarrow> 'process \<Rightarrow> 'residual \<Rightarrow> bool" ("_ \<turnstile> _ \<longmapsto>_" [51, 0, 51] 50)
begin

abbreviation
  transfer :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> ('process \<Rightarrow> 'process \<Rightarrow> bool)"
where
  "transfer \<X> P Q \<equiv> \<forall>\<Gamma> C. \<Gamma> \<turnstile> P \<longmapsto>C \<longrightarrow> (\<exists>D. \<Gamma> \<turnstile> Q \<longmapsto>D \<and> lift \<X> C D)"

lemma transfer_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> transfer \<X> \<le> transfer \<Y>"
  using lift_monotonicity
  by blast

lemma transfer_reverse_weak_equality_preservation: "transfer op = \<ge> op ="
  by (simp add: lift_equality_preservation refl_ge_eq)

lemma transfer_reverse_weak_composition_preservation: "transfer (\<X> OO \<Y>) \<ge> transfer \<X> OO transfer \<Y>"
  using relcomppE and lift_composition_preservation
  by fastforce

lemma transfer_weak_infimum_preservation: "transfer (\<X> \<sqinter> \<Y>) \<le> transfer \<X> \<sqinter> transfer \<Y>"
  by (simp add: transfer_monotonicity)

lemma transfer_reverse_weak_supremum_preservation: "transfer (\<X> \<squnion> \<Y>) \<ge> transfer \<X> \<squnion> transfer \<Y>"
  by (simp add: transfer_monotonicity)

lemma transfer_reflexivity_propagation: "reflp \<X>  \<Longrightarrow> reflp (transfer \<X>)"
  using lift_reflexivity_propagation and reflp_def
  by smt

lemma transfer_transitivity_propagation: "transp \<X> \<Longrightarrow> transp (transfer \<X>)"
  using lift_transitivity_propagation and transp_def
  by smt

abbreviation
  sim :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> bool"
where
  "sim \<X> \<equiv> \<X> \<le> transfer \<X>"

lemma equality_sim_propagation: "sim op ="
  by (fact transfer_reverse_weak_equality_preservation)

lemma composition_sim_propagation: "\<lbrakk> sim \<X>; sim \<Y> \<rbrakk> \<Longrightarrow> sim (\<X> OO \<Y>)"
proof -
  assume "\<X> \<le> transfer \<X>" and "\<Y> \<le> transfer \<Y>"
  then have "\<X> OO \<Y> \<le> transfer \<X> OO transfer \<Y>"
    by (simp add: relcompp_mono)
  moreover have "transfer \<X> OO transfer \<Y> \<le> transfer (\<X> OO \<Y>)"
    by (fact transfer_reverse_weak_composition_preservation)
  ultimately show "\<X> OO \<Y> \<le> transfer (\<X> OO \<Y>)"
    by (fact order.trans)
qed

abbreviation
  bisim :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> bool"
where
  "bisim \<X> \<equiv> sim \<X> \<and> sim \<X>\<inverse>\<inverse>"

lemma equality_bisim_propagation: "bisim op ="
  by (simp add: equality_sim_propagation)

lemma composition_bisim_propagation: "\<lbrakk> bisim \<X>; bisim \<Y> \<rbrakk> \<Longrightarrow> bisim (\<X> OO \<Y>)"
  by (simp add: composition_sim_propagation converse_relcompp)

lemma conversion_bisim_propagation: "bisim \<X> \<Longrightarrow> bisim \<X>\<inverse>\<inverse>"
  by simp

lemma symmetric_simulation: "\<lbrakk> symp \<X>; sim \<X> \<rbrakk> \<Longrightarrow> bisim \<X>"
proof
  assume "symp \<X>"
  then have "\<X>\<inverse>\<inverse> = \<X>"
    using symp_conversep and conversep_le_swap and antisym
    by metis
  moreover assume "sim \<X>"
  ultimately show "sim \<X>\<inverse>\<inverse>"
    by simp
qed

lemma symmetric_closure_of_bisimulation_is_simulation: "bisim \<X> \<Longrightarrow> sim (\<X> \<squnion> \<X>\<inverse>\<inverse>)"
proof -
  assume "bisim \<X>"
  then have "\<X> \<le> transfer \<X>" and "\<X>\<inverse>\<inverse> \<le> transfer \<X>\<inverse>\<inverse>"
    by simp_all
  then have "\<X> \<squnion> \<X>\<inverse>\<inverse> \<le> transfer \<X> \<squnion> transfer \<X>\<inverse>\<inverse>"
    by (fact sup_mono)
  moreover have "transfer \<X> \<squnion> transfer \<X>\<inverse>\<inverse> \<le> transfer (\<X> \<squnion> \<X>\<inverse>\<inverse>)"
    by (fact transfer_reverse_weak_supremum_preservation)
  ultimately show "sim (\<X> \<squnion> \<X>\<inverse>\<inverse>)"
    by (fact order.trans)
qed

coinductive
  pre_bisimilarity :: "'process \<Rightarrow> 'process \<Rightarrow> bool" (infix "\<preceq>" 50)
and
  bisimilarity :: "'process \<Rightarrow> 'process \<Rightarrow> bool" (infix "\<sim>" 50)
where
  "transfer op \<sim> P Q \<Longrightarrow> P \<preceq> Q" |
  "P \<sim> Q \<equiv> P \<preceq> Q \<and> Q \<preceq> P"
monos lift_monotonicity

lemma bisimilarity_symmetry_rule [sym]: "P \<sim> Q \<Longrightarrow> Q \<sim> P"
  by simp

lemma bisimilarity_symmetry: "symp op \<sim>"
  using bisimilarity_symmetry_rule ..

lemma bisimilarity_is_simulation: "sim op \<sim>"
proof -
  have "op \<sim> \<le> op \<preceq>"
    by blast
  moreover have "op \<preceq> \<le> transfer op \<sim>"
    using pre_bisimilarity.cases
    by blast
  ultimately show "op \<sim> \<le> transfer op \<sim>"
    by simp
qed

lemma bisimilarity_is_bisimulation: "bisim op \<sim>"
  using bisimilarity_symmetry and bisimilarity_is_simulation
  by (fact symmetric_simulation)

context begin

private lemma bisimulation_in_pre_bisimilarity: "bisim \<X> \<Longrightarrow> \<X> \<le> op \<preceq>"
proof
  fix P and Q
  assume "bisim \<X>" and "\<X> P Q"
  from `\<X> P Q` have "(\<X> \<squnion> \<X>\<inverse>\<inverse>) P Q"
    by simp
  then show "P \<preceq> Q"
  proof (coinduction arbitrary: P Q)
    case pre_bisimilarity
    with `bisim \<X>` have "transfer (\<X> \<squnion> \<X>\<inverse>\<inverse>) P Q"
      using symmetric_closure_of_bisimulation_is_simulation
      by blast
    moreover
    let
      ?target_relation = "\<lambda>P Q.
        ((\<exists>S T. P = S \<and> Q = T \<and> (\<X> \<squnion> \<X>\<inverse>\<inverse>) S T) \<or> P \<preceq> Q) \<and>
        ((\<exists>S T. Q = S \<and> P = T \<and> (\<X> \<squnion> \<X>\<inverse>\<inverse>) S T) \<or> Q \<preceq> P)"
    have "\<X> \<squnion> \<X>\<inverse>\<inverse> \<le> ?target_relation"
      by blast
    ultimately have "transfer ?target_relation P Q"
      using transfer_monotonicity
      by blast
    then show ?case by simp
  qed
qed

lemma bisimulation_in_bisimilarity: "bisim \<X> \<Longrightarrow> \<X> \<le> op \<sim>"
proof -
  assume "bisim \<X>"
  from `bisim \<X>` have "\<X> \<le> op \<preceq>"
    by (fact bisimulation_in_pre_bisimilarity)
  moreover
  from `bisim \<X>` have "bisim \<X>\<inverse>\<inverse>"
    by (fact conversion_bisim_propagation)
  then have "\<X>\<inverse>\<inverse> \<le> op \<preceq>"
    by (fact bisimulation_in_pre_bisimilarity)
  ultimately show "\<X> \<le> op \<sim>"
    by blast
qed

end

method in_bisimilarity_standard = (
  intro bisimulation_in_bisimilarity,
  intro symmetric_simulation,
  goal_cases symmetry is_simulation
)

lemma bisimilarity_is_greatest_bisimulation: "op \<sim> = (GREATEST \<X>. bisim \<X>)"
  using bisimilarity_is_bisimulation and bisimulation_in_bisimilarity
  by (simp add: Greatest_equality)

context begin

(*
  We put the following into lemmas only to get to choose the names of universally quantified things.
*)

private lemma bisimilarity_standard_symp_intro:
  assumes "(\<And>P Q. \<X> P Q \<Longrightarrow> \<X> Q P)"
  shows "symp \<X>"
  using assms ..

private lemma bisimilarity_standard_sim_intro:
  assumes "(\<And>P Q \<Gamma> C. \<Gamma> \<turnstile> P \<longmapsto>C \<Longrightarrow> \<X> P Q \<Longrightarrow> \<exists>D. \<Gamma> \<turnstile> Q \<longmapsto>D \<and> lift \<X> C D)"
  shows "sim \<X>"
  using assms by blast

method bisimilarity_standard for \<X> :: "'process \<Rightarrow> 'process \<Rightarrow> bool" = (
  (
    intro predicate2D [of \<X> "op \<sim>", rotated];
      match conclusion in
        "\<X> _ _" \<Rightarrow> \<open>succeed\<close> \<bar>
        "\<X> \<le> op \<sim>" \<Rightarrow> \<open>
          (match premises in prems [thin]: _ (multi) \<Rightarrow> \<open>succeed\<close> | succeed);
            in_bisimilarity_standard;
              match conclusion in
                "symp \<X>" \<Rightarrow> \<open>intro bisimilarity_standard_symp_intro\<close> \<bar>
                "sim \<X>" \<Rightarrow> \<open>intro bisimilarity_standard_sim_intro\<close>
        \<close>
  ),
  goal_cases related sym sim
)

end

lemma bisimilarity_reflexivity: "reflp op \<sim>"
proof (unfold reflp_eq, in_bisimilarity_standard)
  case symmetry
  show ?case by (simp add: sympI)
next
  case is_simulation
  show ?case by (fact equality_sim_propagation)
qed

lemma bisimilarity_reflexivity_rule [iff]: "P \<sim> P"
  using bisimilarity_reflexivity ..

lemma bisimilarity_transitivity: "transp op \<sim>"
proof (unfold transp_relcompp, in_bisimilarity_standard)
  case symmetry
  show ?case by (blast intro: sympI)
next
  case is_simulation
  show ?case by (simp add: bisimilarity_is_simulation composition_sim_propagation)
qed

lemma bisimilarity_transitivity_rule [trans]: "\<lbrakk> P \<sim> Q; Q \<sim> R \<rbrakk> \<Longrightarrow> P \<sim> R"
  using bisimilarity_transitivity ..

end

end
