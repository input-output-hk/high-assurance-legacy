section \<open>Transition Systems\<close>

theory Transition_Systems
  imports Residuals "HOL-Eisbach.Eisbach"
begin

subsection \<open>Definition\<close>

text \<open>
  A transition system consists of a notion of residual and a transition relation. There are no
  axioms besides those for \<^term>\<open>lift\<close>.
\<close>

locale transition_system =
  residual lift for lift :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> ('residual \<Rightarrow> 'residual \<Rightarrow> bool)" +
  fixes transition :: "'context \<Rightarrow> 'process \<Rightarrow> 'residual \<Rightarrow> bool" ("_ \<turnstile> _ \<longmapsto>_" [51, 0, 51] 50)
begin

subsection \<open>Transfer\<close>

text \<open>
  We introduce an operation \<open>transfer\<close> that turns a binary relation between processes into a binary
  relation between processes again. A relation \<open>transfer \<X>\<close> relates two processes \<open>P\<close> and~\<open>Q\<close> if
  and only if for each transition from~\<open>P\<close> there is a simulating transition from~\<open>Q\<close> such that the
  target processes of the two transitions are in relation~\<open>\<X>\<close>. The \<open>transfer\<close> operation forms the
  backbone of the definition of simulation relations and is also used in our definition of
  bisimilarity.
\<close>

abbreviation
  transfer :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> ('process \<Rightarrow> 'process \<Rightarrow> bool)"
where
  "transfer \<X> P Q \<equiv> \<forall>\<Gamma> C. \<Gamma> \<turnstile> P \<longmapsto>C \<longrightarrow> (\<exists>D. \<Gamma> \<turnstile> Q \<longmapsto>D \<and> lift \<X> C D)"

text \<open>
  Monotonicity follows from \<^term>\<open>lift\<close> monotonicity.
\<close>

lemma transfer_monotonicity [mono]: "\<X> \<le> \<Y> \<Longrightarrow> transfer \<X> \<le> transfer \<Y>"
  using lift_monotonicity
  by blast

text \<open>
  Reverse weak preservation laws for equality and composition follow from the corresponding
  \<^term>\<open>lift\<close> preservation axioms. There is no reverse weak preservation law for conversion
  because of the fundamental asymmetry in the definition of \<^const>\<open>transfer\<close>.
\<close>

lemma transfer_reverse_weak_equality_preservation: "transfer op = \<ge> op ="
  by (simp add: lift_equality_preservation refl_ge_eq)
lemma transfer_reverse_weak_composition_preservation: "transfer (\<X> OO \<Y>) \<ge> transfer \<X> OO transfer \<Y>"
  by (fastforce simp add: lift_composition_preservation)

text \<open>
  (Reverse) weak preservation laws for the binary infimum and supremum operations follow from just
  the monotonicity axiom, like in the case of \<^term>\<open>lift\<close>.
\<close>

lemma transfer_weak_infimum_preservation: "transfer (\<X> \<sqinter> \<Y>) \<le> transfer \<X> \<sqinter> transfer \<Y>"
  by (simp add: transfer_monotonicity)
lemma transfer_reverse_weak_supremum_preservation: "transfer (\<X> \<squnion> \<Y>) \<ge> transfer \<X> \<squnion> transfer \<Y>"
  by (simp add: transfer_monotonicity)

text \<open>
  Propagation laws for reflexivity and transitivity follow from the corresponding \<^term>\<open>lift\<close>
  propagation laws. There is no propagation law for symmetry because of the fundamental asymmetry in
  the definition of \<^const>\<open>transfer\<close>.
\<close>

lemma transfer_reflexivity_propagation: "reflp \<X>  \<Longrightarrow> reflp (transfer \<X>)"
  using lift_reflexivity_propagation and reflp_def
  by smt
lemma transfer_transitivity_propagation: "transp \<X> \<Longrightarrow> transp (transfer \<X>)"
  using lift_transitivity_propagation and transp_def
  by smt

subsection \<open>Simulation Relations\<close>

text \<open>
  The notion of simulation relation can be defined concisely based on \<^const>\<open>transfer\<close>.
\<close>

abbreviation
  sim :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> bool"
where
  "sim \<X> \<equiv> \<X> \<le> transfer \<X>"

text \<open>
  Equality and composition propagation laws follow from the related reverse weak preservation laws
  of \<^const>\<open>transfer\<close>.
\<close>

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

subsection \<open>Bisimulation Relations\<close>

text \<open>
  The notion of bisimulation relation can be defined concisely based on \<^const>\<open>sim\<close>.
\<close>

abbreviation
  bisim :: "('process \<Rightarrow> 'process \<Rightarrow> bool) \<Rightarrow> bool"
where
  "bisim \<X> \<equiv> sim \<X> \<and> sim \<X>\<inverse>\<inverse>"

text \<open>
  Equality and composition propagation laws follow from the corresponding propagation laws for
  \<^const>\<open>sim\<close>.
\<close>

lemma equality_bisim_propagation: "bisim op ="
  by (simp add: equality_sim_propagation)
lemma composition_bisim_propagation: "\<lbrakk> bisim \<X>; bisim \<Y> \<rbrakk> \<Longrightarrow> bisim (\<X> OO \<Y>)"
  by (simp add: composition_sim_propagation converse_relcompp)

text \<open>
  Conversion propagation follows directly from the definition of \<^const>\<open>bisim\<close>.
\<close>

lemma conversion_bisim_propagation: "bisim \<X> \<Longrightarrow> bisim \<X>\<inverse>\<inverse>"
  by simp

text \<open>
  Any symmetric simulation relation is a bisimulation relation.
\<close>

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

text \<open>
  The symmetric closure of any bisimulation relation is a simulation relation.
\<close>

lemma symmetric_closure_of_bisimulation_is_simulation: "bisim \<X> \<Longrightarrow> sim (\<X> \<squnion> \<X>\<inverse>\<inverse>)"
proof -
  assume "bisim \<X>"
  then have "\<X> \<le> transfer \<X>" and "\<X>\<inverse>\<inverse> \<le> transfer \<X>\<inverse>\<inverse>"
    by simp_all
  then have "\<X> \<squnion> \<X>\<inverse>\<inverse> \<le> transfer \<X> \<squnion> transfer \<X>\<inverse>\<inverse>"
    by (fact sup_mono)
  also have "\<dots> \<le> transfer (\<X> \<squnion> \<X>\<inverse>\<inverse>)"
    by (fact transfer_reverse_weak_supremum_preservation)
  finally show ?thesis .
qed

subsection \<open>Bisimilarity\<close>

text \<open>
  Our definition of bisimilarity is essentially the well-known coinductive definition. Using
  \<^const>\<open>transfer\<close> makes it very concise. As an auxiliary relation we introduce
  ``pre-bisimilarity'', which requires simulation only in one direction for the first step, but in
  both directions for all following steps.
\<close>

coinductive
  pre_bisimilarity :: "'process \<Rightarrow> 'process \<Rightarrow> bool" (infix "\<preceq>" 50)
and
  bisimilarity :: "'process \<Rightarrow> 'process \<Rightarrow> bool" (infix "\<sim>" 50)
where
  "transfer op \<sim> P Q \<Longrightarrow> P \<preceq> Q" |
  "P \<sim> Q \<equiv> P \<preceq> Q \<and> Q \<preceq> P"

subsubsection \<open>Symmetry\<close>

text \<open>
  Symmetry follows directly from the definition of bisimilarity. We introduce two symmetry lemmas:
  one that is phrased using \<open>\<Longrightarrow>\<close> and thus better fits Isabelle's proof tools and one that is
  phrased using the \<^const>\<open>symp\<close> predicate from the @{theory Relation} theory and thus fits
  better our other symmetry-related lemmas and is more concise.
\<close>

lemma bisimilarity_symmetry_rule [sym]: "P \<sim> Q \<Longrightarrow> Q \<sim> P"
  by simp
lemma bisimilarity_symmetry: "symp op \<sim>"
  using bisimilarity_symmetry_rule ..

text \<open>
  We defer reflexivity and transitivity to the
  \hyperref[bisimilarity-reflexivity-transitivity]{end of the bisimilarity subsection} to avoid
  circular reasoning.
\<close>

subsubsection \<open>Bisimilarity as the Greatest Bisimulation Relation\<close>

text \<open>
  Bisimilarity is a simulation relation.
\<close>

lemma bisimilarity_is_simulation: "sim op \<sim>"
proof -
  have "op \<sim> \<le> op \<preceq>"
    by blast
  also have "\<dots> \<le> transfer op \<sim>"
    by (blast elim: pre_bisimilarity.cases)
  finally show ?thesis .
qed

text \<open>
  Bisimilarity is a bisimulation relation.
\<close>

lemma bisimilarity_is_bisimulation: "bisim op \<sim>"
  using bisimilarity_symmetry and bisimilarity_is_simulation
  by (fact symmetric_simulation)

text \<open>
  Any bisimulation relation is a subrelation of bisimilarity.
\<close>

context begin

text \<open>
  We first show the weaker statement that any bisimulation relation is a subrelation of
  \emph{pre}-bisimilarity.
\<close>

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

text \<open>
  With the help of this auxiliary lemma we show the actual statement.
\<close>

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

text \<open>
  This concludes the proof that any bisimulation relation is a subrelation of bisimilarity.
\<close>

end

text \<open>
  From the previous lemmas follows that bisimilarity is the greatest bisimulation relation.
\<close>

lemma bisimilarity_is_greatest_bisimulation: "op \<sim> = (GREATEST \<X>. bisim \<X>)"
  using bisimilarity_is_bisimulation and bisimulation_in_bisimilarity
  by (simp add: Greatest_equality)

subsubsection \<open>Proof Methods\<close>

text \<open>
  Any symmetric simulation relation is a bisimulation relation and thus a subrelation of
  bisimilarity. Based on this fact, we define a standard method for proving statements of the form
  \<^term>\<open>\<X> \<le> op \<sim>\<close>. This method creates two cases: \<open>symmetry\<close>, where \<open>?case\<close> is
  \<^term>\<open>symp \<X>\<close>, and \<open>is_simulation\<close>, where \<open>?case\<close> is \<^term>\<open>sim \<X>\<close>.

  Our proof method can be seen in action in the proofs of \<open>bisimilarity_reflexivity\<close> and
  \<open>bisimilarity_transitivity\<close> in Subsubsection~\ref{bisimilarity-reflexivity-transitivity}.
\<close>

method in_bisimilarity_standard = (
  intro bisimulation_in_bisimilarity,
  intro symmetric_simulation,
  goal_cases symmetry is_simulation
)

text \<open>
  Based on \<open>in_bisimilarity_standard\<close>, we define a method \<open>bisimilarity_standard\<close> for proving
  statements of the form \<open>\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> S \<sim> T\<close>. For any binary process relation~\<open>\<X>\<close>, the
  invocation \<open>(bisimilarity_standard \<X>)\<close> creates the following three cases:

    \<^item> \<open>related\<close>, with premises \<open>A\<^sub>1\<close> to~\<open>A\<^sub>n\<close> and conclusion \<open>\<X> S T\<close>

    \<^item> \<open>sym\<close>, with parameters \<open>P\<close> and~\<open>Q\<close>, premise \<open>\<X> P Q\<close>, and conclusion \<open>\<X> Q P\<close>

    \<^item> \<open>sim\<close>, with parameters \<open>P\<close>, \<open>Q\<close>, \<open>\<Gamma>\<close>, and \<open>C\<close>, premises \<open>\<Gamma> \<turnstile> P \<longmapsto>C\<close> and \<open>\<X> P Q\<close>, and
      conclusion \<open>\<exists>D. \<Gamma> \<turnstile> Q \<longmapsto>D \<and> lift \<X> C D\<close>

  Note that, contrary to the \<open>symmetry\<close> and \<open>is_simulation\<close> cases of \<open>in_bisimilarity_standard\<close>, the
  \<open>sym\<close> and \<open>sim\<close> cases of \<open>bisimilarity_standard\<close> do not use the \<^term>\<open>symp\<close> and \<^term>\<open>sim\<close>
  predicates but make the underlying logical constructions explicit. This often makes proofs easier.
  Furthermore note that in the \<open>sim\<close> case the premise \<open>\<Gamma> \<turnstile> P \<longmapsto>C\<close> comes before the premise
  \<open>\<X> P Q\<close>. In the common situation of an inductively defined \<open>transition\<close> relation, this
  arrangement makes it possible to directly handle the \<open>sim\<close> case via induction on \<open>\<Gamma> \<turnstile> P \<longmapsto>C\<close>, by
  writing \<^theory_text>\<open>then show ?case proof induction \<dots> qed\<close>.
\<close>

context begin

text \<open>
  We introduce two trivial auxiliary lemmas, which are used by the \<open>bisimilarity_standard\<close> proof
  method. It would be simpler to let \<open>bisimilarity_standard\<close> employ some simple proof methods
  instead of using these lemmas. However, the present solution allows us to choose default names for
  the parameters of the \<open>sym\<close> and \<open>sim\<close> cases.
\<close>

private lemma bisimilarity_standard_symp_intro:
  assumes "(\<And>P Q. \<X> P Q \<Longrightarrow> \<X> Q P)"
  shows "symp \<X>"
  using assms ..
private lemma bisimilarity_standard_sim_intro:
  assumes "(\<And>P Q \<Gamma> C. \<lbrakk> \<Gamma> \<turnstile> P \<longmapsto>C; \<X> P Q \<rbrakk> \<Longrightarrow> \<exists>D. \<Gamma> \<turnstile> Q \<longmapsto>D \<and> lift \<X> C D)"
  shows "sim \<X>"
  using assms by blast

text \<open>
  With the help of these auxiliary lemmas we define the proof method.
\<close>

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

text \<open>
  This concludes the definition of the standard proof method for bisimilarity.
\<close>

end

subsubsection \<open>Reflexivity and Transitivity\label{bisimilarity-reflexivity-transitivity}\<close>

text \<open>
  Reflexivity follows from equality propagation for \<^const>\<open>sim\<close>. Analogously to our handling of
  symmetry, we introduce two reflexivity lemmas: one that is phrased using the \<^const>\<open>reflp\<close>
  predicate from the @{theory Relation} theory and one that is phrased more explicitly.
\<close>

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

text \<open>
  Transitivity follows from composition propagation for \<^const>\<open>sim\<close>. Again, we introduce two
  lemmas.
\<close>

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

subsection \<open>Conclusion\<close>

text \<open>
  This is all for transition systems.
\<close>

end
end
