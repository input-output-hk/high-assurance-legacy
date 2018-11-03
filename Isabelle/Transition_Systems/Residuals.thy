section \<open>Residuals\label{residuals}\<close>

theory Residuals
  imports Main "HOL-Library.Lattice_Syntax" "HOL-Eisbach.Eisbach"
begin

text \<open>
  Since binders in a label may bind their names also in the target process, we bundle the label and
  the target process of a transition and call the resulting bundle a residual. Because transition
  systems differ in the binding structures they allow, we cannot define a single data type of
  residuals. Instead we define a notion of residual axiomatically.

  Our definition is based on an operation \<open>lift\<close> that turns a binary relation between processes into
  a binary relation between residuals. The idea is that \<open>lift \<X>\<close> relates two residuals \<open>d\<close> and~\<open>e\<close>
  if and only if the labels of \<open>d\<close> and~\<open>e\<close> are identical and the target processes of \<open>d\<close> and~\<open>e\<close> are
  in relation~\<open>\<X>\<close>. This idea comes from the definitions of simulation relations and related
  concepts.

  In the presence of scope openings there is no clear separation between the label and the target
  process of a residual because there are binding structures that span both of them. Using HOAS,
  such binding structures are represented by functions. For example, in a suitable HOAS variant of
  the $\pi$-calculus, the residual of a transition $\openandsendexample$ is \<open>OpenAndSend x (\<lambda>y. q)\<close>,
  where \<open>OpenAndSend\<close> is a data constructor. The function \<open>\<lambda>y. q\<close> does not belong to only the label
  or the target process but constitutes part of the label and the complete target process.

  Nevertheless we can still identify a label and a target process in the term structure of such a
  residual: in the above example the label is \<open>x (\<lambda>y. _)\<close> and the target process is~\<open>q\<close>. Based on
  this observation, we can apply the idea about the \<open>lift\<close> operation to residuals with scope
  openings. For our $\pi$-calculus example, we define that a relation \<open>lift \<X>\<close> relates residuals
  \<open>OpenAndSend x\<^sub>1 Q\<^sub>1\<close> and \<open>OpenAndSend x\<^sub>2 Q\<^sub>2\<close> if and only if \<open>x\<^sub>1 = x\<^sub>2\<close> and \<open>\<And>y. \<X> (Q\<^sub>1 y) (Q\<^sub>2 y)\<close>.
  Since \<open>OpenAndSend x\<^sub>i Q\<^sub>i\<close> is the same as \<open>OpenSend x\<^sub>i (\<lambda>y. Q\<^sub>i y)\<close>, these conditions just mean that
  the labels \<open>x\<^sub>1 (\<lambda>y. _)\<close> and \<open>x\<^sub>2 (\<lambda>y. _)\<close> are identical and the target processes \<open>Q\<^sub>1 y\<close> and \<open>Q\<^sub>2 y\<close>
  are in relation~\<open>\<X>\<close> independently of~\<open>y\<close>; so those conditions are in line with our idea about
  \<open>lift\<close>. For other kinds of residuals, \<open>lift\<close> shall work analogously.

  We choose the residual axioms such that they are naturally fulfilled by \<open>lift\<close> operations that
  work as described above. Our axioms may be fulfilled also by other kinds of \<open>lift\<close> operations and
  thus be more permissive than expected. This is not a problem, however, because all desired lemmas
  about transition systems can be derived from these axioms.
\<close>

locale residual =
  fixes lift :: "(['process, 'process] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)"
  assumes lift_monotonicity [mono]:
    "\<X> \<le> \<Y> \<Longrightarrow> lift \<X> \<le> lift \<Y>"
  assumes lift_equality_preservation:
    "lift (=) = (=)"
  assumes lift_composition_preservation:
    "lift (\<X> OO \<Y>) = lift \<X> OO lift \<Y>"
  assumes lift_conversion_preservation:
    "lift \<X>\<inverse>\<inverse> = (lift \<X>)\<inverse>\<inverse>"
begin

text \<open>
  Using \<open>lift_monotonicity\<close>, we define a proof method for reasoning under \<^term>\<open>lift\<close>. This
  method expects a fact of the form \<^term>\<open>lift \<X> d e\<close> and a goal of the form
  \<^term>\<open>lift \<Y> d e\<close> and generates the subgoal \<^term>\<open>\<And>p q. \<X> p q \<Longrightarrow> \<Y> p q\<close>.
\<close>

method under_lift = (elim predicate2D [OF lift_monotonicity, OF predicate2I, rotated])

text \<open>
  (Reverse) weak preservation laws for the binary infimum and supremum operations follow from just
  the monotonicity axiom. This has nothing to do with the particularities of binary relations but
  relies solely on the fact that binary relations form a lattice.
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
