section \<open>Residuals\<close>

theory Residuals
  imports Main "HOL-Library.Lattice_Syntax"
begin

text \<open>
  Since binders in a label may bind their names also in the target process, we bundle the label and
  the target process of a transition and call the resulting bundle a residual. Because transition
  systems differ in the binding structures they allow, we cannot define a single data type of
  residuals. Instead we define a notion of residual axiomatically.

  Our definition is based on an operation \<open>lift\<close> that turns a binary relation between processes into
  a binary relation between residuals. The general idea is that \<open>lift \<X>\<close> relates two residuals \<open>C\<close>
  and~\<open>D\<close> if and only if the labels of \<open>C\<close> and~\<open>D\<close> are identical and the target processes of \<open>C\<close>
  and~\<open>D\<close> are in relation~\<open>\<X>\<close>. This idea comes from the definitions of simulation and bisimulation
  relations. In the presence of scope openings, the described relationship between \<open>C\<close> and~\<open>D\<close> has
  to exist only up to $\alpha$-conversion.

  We choose the residual axioms such that they are naturally fulfilled by \<open>lift\<close> operations that
  work as described above. Our axioms may be fulfilled also by other kinds of \<open>lift\<close> operations.
\<close>

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

text \<open>
  (Reverse) weak preservation laws for the binary infimum and supremum operations follow from just
  the monotonicity axiom.
\<close>

lemma lift_weak_infimum_preservation: "lift (\<X> \<sqinter> \<Y>) \<le> lift \<X> \<sqinter> lift \<Y>"
  by (simp add: lift_monotonicity)
lemma lift_reverse_weak_supremum_preservation: "lift (\<X> \<squnion> \<Y>) \<ge> lift \<X> \<squnion> lift \<Y>"
  by (simp add: lift_monotonicity)

text \<open>
  Propagation laws for reflexivity, transitivity, and symmetry each follow from monotonicity and one
  of the preservation axioms.
\<close>

lemma lift_reflexivity_propagation: "reflp \<X> \<Longrightarrow> reflp (lift \<X>)"
  using reflp_eq and lift_monotonicity and lift_equality_preservation
  by metis
lemma lift_transitivity_propagation: "transp \<X> \<Longrightarrow> transp (lift \<X>)"
  using transp_relcompp and lift_monotonicity and lift_composition_preservation
  by metis
lemma lift_symmetry_propagation: "symp \<X> \<Longrightarrow> symp (lift \<X>)"
  using symp_conversep and lift_monotonicity and lift_conversion_preservation
  by metis

text \<open>
  This is all for residuals.
\<close>

end
end
