section \<open>Transition Systems\<close>

theory Transition_Systems
  imports Simulation_Systems
begin

text \<open>
  A transition system is characterized by a notion of residual and a single transition relation.
\<close>

locale transition_system =
  residual lift for lift :: "(['process, 'process] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)" +
  fixes transition :: "['process, 'residual] \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 50)
begin

subsection \<open>Relationship to Simulation Systems\<close>

text \<open>
  A transition system is a simulation system whose original and simulating transition relation are
  the same.
\<close>

sublocale simulation_system lift transition transition
  by intro_locales

subsection \<open>Transfer\<close>

text \<open>
  Reverse weak preservation laws for equality and composition follow from the corresponding
  \<^term>\<open>lift\<close> preservation axioms.
\<close>

lemma transfer_reverse_weak_equality_preservation:
  "transfer (=) \<ge> (=)"
  by (simp add: lift_equality_preservation refl_ge_eq)
lemma transfer_reverse_weak_composition_preservation:
  "transfer (\<X> OO \<Y>) \<ge> transfer \<X> OO transfer \<Y>"
  by (fastforce simp add: lift_composition_preservation)

text \<open>
  There is no reverse weak preservation law for conversion because of the fundamental asymmetry in
  the definition of \<^const>\<open>transfer\<close>.
\<close>

text \<open>
  Propagation laws for reflexivity and transitivity follow from the corresponding \<^term>\<open>lift\<close>
  propagation laws.
\<close>

lemma transfer_reflexivity_propagation: "reflp \<X>  \<Longrightarrow> reflp (transfer \<X>)"
  using lift_reflexivity_propagation and reflp_def
  by smt
lemma transfer_transitivity_propagation: "transp \<X> \<Longrightarrow> transp (transfer \<X>)"
  using lift_transitivity_propagation and transp_def
  by smt

text \<open>
  There is no propagation law for symmetry because of the fundamental asymmetry in the definition
  of \<^const>\<open>transfer\<close>.
\<close>

subsection \<open>Simulation Relations\<close>

text \<open>
  Equality and composition propagation laws follow from the related reverse weak preservation laws
  of \<^const>\<open>transfer\<close>.
\<close>

lemma equality_sim_propagation: "sim (=)"
  by (fact transfer_reverse_weak_equality_preservation)
lemma composition_sim_propagation: "\<lbrakk> sim \<X>; sim \<Y> \<rbrakk> \<Longrightarrow> sim (\<X> OO \<Y>)"
proof -
  assume "\<X> \<le> transfer \<X>" and "\<Y> \<le> transfer \<Y>"
  then have "\<X> OO \<Y> \<le> transfer \<X> OO transfer \<Y>"
    by (fact relcompp_mono)
  also have "transfer \<X> OO transfer \<Y> \<le> transfer (\<X> OO \<Y>)"
    by (fact transfer_reverse_weak_composition_preservation)
  finally show ?thesis .
qed

text \<open>
  Equality and composition propagation laws follow from the corresponding propagation laws for
  \<^const>\<open>sim\<close>.
\<close>

lemma equality_bisim_propagation: "bisim (=)"
  by (simp add: equality_sim_propagation)
lemma composition_bisim_propagation: "\<lbrakk> bisim \<X>; bisim \<Y> \<rbrakk> \<Longrightarrow> bisim (\<X> OO \<Y>)"
  by (simp add: composition_sim_propagation converse_relcompp)

subsection \<open>Bisimilarity\<close>

text \<open>
  We introduce the same infix operators for \<^const>\<open>pre_bisimilarity\<close> and \<^const>\<open>bisimilarity\<close>
  as \<open>simulation_system\<close>.
\<close>

notation pre_bisimilarity (infix \<open>\<lesssim>\<close> 50)
notation bisimilarity (infix \<open>\<sim>\<close> 50)

subsubsection \<open>Reflexivity and Transitivity\<close>

text \<open>
  Reflexivity follows from equality propagation for \<^const>\<open>sim\<close>. Analogously to our handling of
  symmetry, we introduce two reflexivity lemmas: one that is phrased using the \<^const>\<open>reflp\<close>
  predicate from the @{theory HOL.Relation} theory and one that is phrased more explicitly.
\<close>

lemma bisimilarity_reflexivity: "reflp (\<sim>)"
unfolding reflp_eq proof in_bisimilarity_standard
  case symmetry
  show ?case by (simp add: symp_def)
next
  case is_simulation
  show ?case by (fact equality_sim_propagation)
qed
lemma bisimilarity_reflexivity_rule [iff]: "p \<sim> p"
  using bisimilarity_reflexivity ..

text \<open>
  Transitivity follows from composition propagation for \<^const>\<open>sim\<close>. Again, we introduce two
  lemmas.
\<close>

lemma bisimilarity_transitivity: "transp (\<sim>)"
unfolding transp_relcompp proof in_bisimilarity_standard
  case symmetry
  show ?case
    unfolding symp_def and bisimilarity_def
    by blast
next
  case is_simulation
  show ?case by (simp add: bisimilarity_is_simulation composition_sim_propagation)
qed
lemma bisimilarity_transitivity_rule [trans]: "\<lbrakk> p \<sim> q; q \<sim> r \<rbrakk> \<Longrightarrow> p \<sim> r"
  using bisimilarity_transitivity ..

subsubsection \<open>Bisimilarity as an Equivalence Relation\<close>

lemma bisimilarity_is_equivalence:
  shows "equivp (\<sim>)"
  by
    (intro equivpI)
    (fact bisimilarity_reflexivity, fact bisimilarity_symmetry, fact bisimilarity_transitivity)

subsection \<open>Conclusion\<close>

text \<open>
  This is all for transition systems.
\<close>

end
end
