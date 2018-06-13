section \<open>Residuals\<close>

theory Residuals
  imports Main "HOL-Library.Lattice_Syntax"
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

end
