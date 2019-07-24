section \<open>Simulation Systems\<close>

theory Simulation_Systems
  imports Residuals "HOL-Eisbach.Eisbach"
begin

text \<open>
  A simulation system is characterized by a notion of residual and two transition relations.
\<close>

locale simulation_system =
  residual lift for lift :: "(['process, 'process] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)" +
  fixes original_transition :: "['process, 'residual] \<Rightarrow> bool" (infix "\<rightharpoonup>" 50)
  fixes simulating_transition :: "['process, 'residual] \<Rightarrow> bool" (infix "\<rightharpoondown>" 50)
begin

subsection \<open>Transfer\<close>

text \<open>
  We introduce an operation \<open>transfer\<close> that turns a binary relation between processes into a binary
  relation between processes again. A relation \<open>transfer \<X>\<close> relates two processes \<open>p\<close> and~\<open>q\<close> if
  and only if for each original transition from~\<open>p\<close> there is a simulating transition from~\<open>q\<close> such
  that the target processes of the two transitions are in relation~\<open>\<X>\<close>. The \<open>transfer\<close> operation
  forms the backbone of our definition of simulation relations and is also used in our definition of
  bisimilarity.
\<close>

abbreviation
  transfer :: "(['process, 'process] \<Rightarrow> bool) \<Rightarrow> (['process, 'process] \<Rightarrow> bool)"
where
  "transfer \<X> p q \<equiv> \<forall>c. p \<rightharpoonup> c \<longrightarrow> (\<exists>d. q \<rightharpoondown> d \<and> lift \<X> c d)"

text \<open>
  Monotonicity of \<^term>\<open>transfer\<close> follows from monotonicity of \<^term>\<open>lift\<close>.
\<close>

lemma transfer_monotonicity [mono]: "\<X> \<le> \<Y> \<Longrightarrow> transfer \<X> \<le> transfer \<Y>"
  using lift_monotonicity
  by blast

text \<open>
  (Reverse) weak preservation laws for the binary infimum and supremum operations follow from just
  the monotonicity lemma, like in the case of \<^term>\<open>lift\<close>.
\<close>

lemma transfer_weak_infimum_preservation:
  "transfer (\<X> \<sqinter> \<Y>) \<le> transfer \<X> \<sqinter> transfer \<Y>"
  by (simp add: transfer_monotonicity)
lemma transfer_reverse_weak_supremum_preservation:
  "transfer (\<X> \<squnion> \<Y>) \<ge> transfer \<X> \<squnion> transfer \<Y>"
  by (simp add: transfer_monotonicity)

subsection \<open>Simulation Relations\<close>

text \<open>
  The notion of simulation relation can be defined concisely based on \<^const>\<open>transfer\<close>.
\<close>

abbreviation
  sim :: "(['process, 'process] \<Rightarrow> bool) \<Rightarrow> bool"
where
  "sim \<X> \<equiv> \<X> \<le> transfer \<X>"

subsection \<open>Bisimulation Relations\<close>

text \<open>
  The notion of bisimulation relation can be defined concisely based on \<^const>\<open>sim\<close>.
\<close>

abbreviation
  bisim :: "(['process, 'process] \<Rightarrow> bool) \<Rightarrow> bool"
where
  "bisim \<X> \<equiv> sim \<X> \<and> sim \<X>\<inverse>\<inverse>"

text \<open>
  Conversion propagation follows directly from the definition of \<^const>\<open>bisim\<close>.
\<close>

lemma conversion_bisim_propagation: "bisim \<X> \<Longrightarrow> bisim \<X>\<inverse>\<inverse>"
  by simp

text \<open>
  Any symmetric simulation relation is a bisimulation relation.
\<close>

lemma symmetric_simulation_is_bisimulation: "\<lbrakk> symp \<X>; sim \<X> \<rbrakk> \<Longrightarrow> bisim \<X>"
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
  \<open>\<close>pre-bisimilarity'', which requires simulation only in one direction for the first step but in
  both directions for all following steps.
\<close>

coinductive
  pre_bisimilarity :: "['process, 'process] \<Rightarrow> bool" (infix "\<lesssim>" 50)
where
  pre_bisimilarity: "transfer (\<lambda>p q. p \<lesssim> q \<and> q \<lesssim> p) p q \<Longrightarrow> p \<lesssim> q"

definition bisimilarity :: "['process, 'process] \<Rightarrow> bool" (infix "\<sim>" 50) where
  "p \<sim> q \<equiv> p \<lesssim> q \<and> q \<lesssim> p"

subsubsection \<open>Symmetry\<close>

text \<open>
  Symmetry follows directly from the definition of bisimilarity. We introduce two symmetry lemmas:
  one that is phrased using \<open>\<Longrightarrow>\<close> and thus better fits Isabelle's proof tools and one that is
  phrased using the \<^const>\<open>symp\<close> predicate from the @{theory HOL.Relation} theory and thus fits
  better our other symmetry-related lemmas and is more concise.
\<close>

lemma bisimilarity_symmetry_rule [sym]: "p \<sim> q \<Longrightarrow> q \<sim> p"
  by (simp add: bisimilarity_def)
lemma bisimilarity_symmetry: "symp (\<sim>)"
  using bisimilarity_symmetry_rule ..

subsubsection \<open>Bisimilarity as the Greatest Bisimulation Relation\<close>

text \<open>
  Bisimilarity is a simulation relation.
\<close>

lemma bisimilarity_is_simulation: "sim (\<sim>)"
  unfolding bisimilarity_def
  by (blast elim: pre_bisimilarity.cases)

text \<open>
  Bisimilarity is a bisimulation relation.
\<close>

lemma bisimilarity_is_bisimulation: "bisim (\<sim>)"
  using bisimilarity_symmetry and bisimilarity_is_simulation
  by (fact symmetric_simulation_is_bisimulation)

text \<open>
  Any bisimulation relation is a subrelation of bisimilarity.
\<close>

context begin

text \<open>
  We first show the weaker statement that any bisimulation relation is a subrelation of
  \emph{pre}-bisimilarity.
\<close>

private lemma bisimulation_in_pre_bisimilarity: "bisim \<X> \<Longrightarrow> \<X> \<le> (\<lesssim>)"
proof
  fix p and q
  assume "bisim \<X>" and "\<X> p q"
  from \<open>\<X> p q\<close> have "(\<X> \<squnion> \<X>\<inverse>\<inverse>) p q"
    by simp
  then show "p \<lesssim> q"
  proof (coinduction arbitrary: p q)
    case pre_bisimilarity
    with \<open>bisim \<X>\<close> have "transfer (\<X> \<squnion> \<X>\<inverse>\<inverse>) p q"
      using symmetric_closure_of_bisimulation_is_simulation
      by blast
    moreover
    let
      ?target_relation = "\<lambda>p q.
        ((\<exists>s t. p = s \<and> q = t \<and> (\<X> \<squnion> \<X>\<inverse>\<inverse>) s t) \<or> p \<lesssim> q) \<and>
        ((\<exists>s t. q = s \<and> p = t \<and> (\<X> \<squnion> \<X>\<inverse>\<inverse>) s t) \<or> q \<lesssim> p)"
    have "\<X> \<squnion> \<X>\<inverse>\<inverse> \<le> ?target_relation"
      by blast
    ultimately have "transfer ?target_relation p q"
      using transfer_monotonicity
      by blast
    then show ?case by simp
  qed
qed

text \<open>
  With the help of this auxiliary lemma we show the actual statement.
\<close>

lemma bisimulation_in_bisimilarity: "bisim \<X> \<Longrightarrow> \<X> \<le> (\<sim>)"
proof -
  assume "bisim \<X>"
  from \<open>bisim \<X>\<close> have "\<X> \<le> (\<lesssim>)"
    by (fact bisimulation_in_pre_bisimilarity)
  moreover
  from \<open>bisim \<X>\<close> have "bisim \<X>\<inverse>\<inverse>"
    by (fact conversion_bisim_propagation)
  then have "\<X>\<inverse>\<inverse> \<le> (\<lesssim>)"
    by (fact bisimulation_in_pre_bisimilarity)
  ultimately show "\<X> \<le> (\<sim>)"
    unfolding bisimilarity_def
    by blast
qed

text \<open>
  This concludes the proof that any bisimulation relation is a subrelation of bisimilarity.
\<close>

end

text \<open>
  From the previous lemmas follows that bisimilarity is the greatest bisimulation relation.
\<close>

lemma bisimilarity_is_greatest_bisimulation: "(\<sim>) = (GREATEST \<X>. bisim \<X>)"
  using bisimilarity_is_bisimulation and bisimulation_in_bisimilarity
  by (simp add: Greatest_equality)

subsubsection \<open>Proof Methods\<close>

text \<open>
  We define a method \<open>bisimilarity_standard\<close> for proving statements of the form
  \<open>\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> s \<sim> t\<close>. For any binary process relation~\<open>\<X>\<close>, the invocation
  \<open>(bisimilarity_standard \<X>)\<close> creates the following two cases:

    \<^item> \<open>related\<close>, with premises \<open>A\<^sub>1\<close> to~\<open>A\<^sub>n\<close> and conclusion \<open>\<X> s t\<close>

    \<^item> \<open>in_bisimilarity\<close>, with conclusion \<^term>\<open>\<X> \<le> (\<sim>)\<close>
\<close>

method bisimilarity_standard for \<X> :: "['process, 'process] \<Rightarrow> bool" = (
  (
    intro predicate2D [of \<X> "(\<sim>)", rotated];
      match conclusion in
        "\<X> _ _" (cut) \<Rightarrow> \<open>succeed\<close> \<bar>
        "\<X> \<le> (\<sim>)" (cut) \<Rightarrow> \<open>match premises in prems [thin]: _ (cut, multi) \<Rightarrow> \<open>succeed\<close> | succeed\<close>
  ),
  goal_cases related in_bisimilarity
)

text \<open>
  Any symmetric simulation relation is a bisimulation relation and thus a subrelation of
  bisimilarity. Based on this fact, we define a method \<open>in_bisimilarity_standard\<close> for proving
  statements of the form \<^term>\<open>\<X> \<le> (\<sim>)\<close>. This method creates the following two cases:

    \<^item> \<open>symmetry\<close>, with conclusion \<^term>\<open>symp \<X>\<close>

    \<^item> \<open>is_simulation\<close>, with conclusion \<^term>\<open>sim \<X>\<close>
\<close>

method in_bisimilarity_standard = (
  intro bisimulation_in_bisimilarity,
  intro symmetric_simulation_is_bisimulation,
  goal_cases symmetry is_simulation
)

text \<open>
  We define a method \<open>is_simulation_standard\<close> for proving statements of the form \<^term>\<open>sim \<X>\<close>. This
  method creates the following single case:

    \<^item> \<open>sim\<close>, with parameters \<open>p\<close>, \<open>q\<close>, and \<open>c\<close>, premises \<^term>\<open>s \<rightharpoonup> c\<close> and \<^term>\<open>\<X> p q\<close>, and
      conclusion \<^term>\<open>\<exists>d. q \<rightharpoondown> d \<and> lift \<X> c d\<close>

  Note that the premise \<^term>\<open>p \<rightharpoonup> c\<close> of the \<open>sim\<close> case comes before the premise \<^term>\<open>\<X> p q\<close>. In
  the common situation of an inductively defined relation~\<^term>\<open>(\<rightharpoonup>)\<close>, this arrangement makes it
  possible to directly handle the \<open>sim\<close> case via induction on the derivation of \<open>p \<rightharpoonup> c\<close>, by writing
  @{theory_text \<open>then show ?case proof induction \<dots> qed\<close>}.
\<close>

context begin

text \<open>
  We introduce a trivial auxiliary lemma, which is used by the \<open>is_simulation_standard\<close> proof
  method. It would be simpler to let \<open>is_simulation_standard\<close> employ some basic proof methods
  instead of using this lemma. However, the present solution allows us to choose default names for
  the parameters of the \<open>sim\<close> case.
\<close>

text \<open>
  Actually, we would like to use \<^term>\<open>\<And>p q c. \<lbrakk>p \<rightharpoonup> c; \<X> p q\<rbrakk> \<Longrightarrow> \<exists>d. q \<rightharpoondown> d \<and> lift \<X> c d\<close> as the
  assumption and \<^term>\<open>sim \<X>\<close> as the thesis. However, because of the presumed bug described at
  \url{https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2019-February/msg00024.html} we use a
  sloppier definition. This definition has the advantage that it is independent from the concrete
  locale interpretation. As a result we get the correct behavior even if Isabelle picks the method
  from the wrong interpretation.
\<close>

private lemma is_simulation_standard_sim_intro:
  assumes "
    \<And>p q c.
    \<lbrakk>original_transition_dummy p c; \<X> p q\<rbrakk> \<Longrightarrow>
    \<exists>d. simulating_transition_dummy q d \<and> lift_dummy \<X> c d"
  shows "
    \<X> \<le> (
      \<lambda>p q. (
        \<forall>c.
        original_transition_dummy p c \<longrightarrow>
        (\<exists>d. simulating_transition_dummy q d \<and> lift_dummy \<X> c d)
      )
    )"
  using assms
  by blast

text \<open>
  With the help of this auxiliary lemma we define the proof method.
\<close>

method is_simulation_standard = (intro is_simulation_standard_sim_intro, goal_cases sim)

text \<open>
  This concludes the definition of the standard proof method for bisimilarity.
\<close>

end

subsection \<open>Conclusion\<close>

text \<open>
  This is all for simulation systems.
\<close>

end
end
