theory "Transition_Systems-Mutation_Systems"
imports
  "Transition_Systems-Simulation_Systems"
begin

primrec with_shortcut :: "('a \<Rightarrow> 'p relation) \<Rightarrow> ('a option \<Rightarrow> 'p relation)" where
  "with_shortcut \<T> None = (=)" |
  "with_shortcut \<T> (Some \<alpha>) = \<T> \<alpha>"

locale mutation_system =
  simulation_system \<open>original_transition\<close> \<open>simulating_transition\<close>
  for
    original_transition :: "'a \<Rightarrow> 'p relation" (\<open>'(\<rightharpoonup>\<lparr>_\<rparr>')\<close>)
  and
    simulating_transition :: "'a \<Rightarrow> 'p relation" (\<open>'(\<rightharpoondown>\<lparr>_\<rparr>')\<close>)
  +
  fixes
    original_shortcut_transition :: "'a option \<Rightarrow> 'p relation" (\<open>'(\<rightharpoonup>\<^sup>?\<lparr>_\<rparr>')\<close>)
  fixes
    simulating_shortcut_transition :: "'a option \<Rightarrow> 'p relation" (\<open>'(\<rightharpoondown>\<^sup>?\<lparr>_\<rparr>')\<close>)
  fixes
    universe :: "'p relation set" (\<open>\<U>\<close>)
  fixes
    mutation_transition_std :: "'p relation \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> 'p relation \<Rightarrow> bool"
    (\<open>(_ \<longrightarrow>\<lparr>_ \<bar> _\<rparr>/ _)\<close> [51, 0, 0, 51] 50)
  defines original_shortcut_transition_def [simp]:
    "original_shortcut_transition \<equiv> with_shortcut original_transition"
  defines simulating_shortcut_transition_def [simp]:
    "simulating_shortcut_transition \<equiv> with_shortcut simulating_transition"
  assumes mutation_transition_std_is_type_correct:
    "\<And>\<alpha> \<omega> I J. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J \<Longrightarrow> I \<in> \<U> \<and> J \<in> \<U>"
  assumes dissection:
    "\<And>\<alpha>. \<forall>I \<in> \<U>. I OO (\<rightharpoonup>\<lparr>\<alpha>\<rparr>) \<le> \<Squnion> {(\<rightharpoonup>\<^sup>?\<lparr>\<omega>\<rparr>) OO J | \<omega> J. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J}"
  assumes connection:
    "\<And>\<alpha>. \<forall>J \<in> \<U>. \<Squnion> {I\<inverse>\<inverse> OO (\<rightharpoondown>\<^sup>?\<lparr>\<omega>\<rparr>) | \<omega> I. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J} \<le> (\<rightharpoondown>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>"
begin

text \<open>
  The introduction of an explicit \<^term>\<open>mutation_transition_std\<close> relation has the following
  advantages:

    \<^item> We can replace Sangiorgi's seemingly \<^emph>\<open>ad hoc\<close> condition by a pair of conditions that are in
      perfect duality.

    \<^item> We can refer from the outside to the data that is only guaranteed to exist in the case of
      Sangiorgi's condition. This is crucial for the specification of weak mutation systems.
\<close>

definition mutant_lifting :: "'p relation \<Rightarrow> 'p relation" (\<open>\<M>\<close>) where
  [simp]: "\<M> = (\<lambda>K. (\<Squnion>I \<in> \<U>. I\<inverse>\<inverse> OO K OO I))"

context begin

text \<open>
  This is the place where we finally need the extra condition \<^term>\<open>K \<le> L\<close> that sets apart
  \<^term>\<open>K \<leadsto> L\<close> from \<^term>\<open>K \<mapsto> L\<close>.
\<close>

private lemma unilateral_shortcut_progression:
  assumes "K \<le> L" and "K \<hookrightarrow> L"
  shows "K\<inverse>\<inverse> OO (\<rightharpoonup>\<^sup>?\<lparr>\<omega>\<rparr>) \<le> (\<rightharpoondown>\<^sup>?\<lparr>\<omega>\<rparr>) OO L\<inverse>\<inverse>"
  using assms by (cases \<omega>) auto

private lemma unilateral_mutant_progression:
  assumes "K \<le> L" and "K \<hookrightarrow> L"
  shows "\<M> K \<hookrightarrow> \<M> L"
proof -
  have "(\<Squnion>I \<in> \<U>. I\<inverse>\<inverse> OO K OO I)\<inverse>\<inverse> OO (\<rightharpoonup>\<lparr>\<alpha>\<rparr>) \<le> (\<rightharpoondown>\<lparr>\<alpha>\<rparr>) OO (\<Squnion>J \<in> \<U>. J\<inverse>\<inverse> OO L OO J)\<inverse>\<inverse>" for \<alpha>
  proof -
    have "(\<Squnion>I \<in> \<U>. I\<inverse>\<inverse> OO K OO I)\<inverse>\<inverse> OO (\<rightharpoonup>\<lparr>\<alpha>\<rparr>) = (\<Squnion>I \<in> \<U>. I\<inverse>\<inverse> OO K\<inverse>\<inverse> OO I) OO (\<rightharpoonup>\<lparr>\<alpha>\<rparr>)"
      by blast
    also have "\<dots> = (\<Squnion>I \<in> \<U>. I\<inverse>\<inverse> OO K\<inverse>\<inverse> OO I OO (\<rightharpoonup>\<lparr>\<alpha>\<rparr>))"
      by blast
    also have "\<dots> \<le> (\<Squnion>I \<in> \<U>. I\<inverse>\<inverse> OO K\<inverse>\<inverse> OO \<Squnion> {(\<rightharpoonup>\<^sup>?\<lparr>\<omega>\<rparr>) OO J | \<omega> J. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J})"
      using dissection
      by simp fast
    also have "\<dots> = (\<Squnion>I \<in> \<U>. \<Squnion> {I\<inverse>\<inverse> OO K\<inverse>\<inverse> OO (\<rightharpoonup>\<^sup>?\<lparr>\<omega>\<rparr>) OO J | \<omega> J. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J})"
      by blast
    also have "\<dots> = \<Squnion> {I\<inverse>\<inverse> OO K\<inverse>\<inverse> OO (\<rightharpoonup>\<^sup>?\<lparr>\<omega>\<rparr>) OO J | \<omega> I J. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J}"
      using mutation_transition_std_is_type_correct
      by blast
    also have "\<dots> \<le> \<Squnion> {I\<inverse>\<inverse> OO (\<rightharpoondown>\<^sup>?\<lparr>\<omega>\<rparr>) OO L\<inverse>\<inverse> OO J | \<omega> I J. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J}"
      using unilateral_shortcut_progression [OF \<open>K \<le> L\<close> \<open>K \<hookrightarrow> L\<close>]
      by blast
    also have "\<dots> = (\<Squnion>J \<in> \<U>. \<Squnion> {I\<inverse>\<inverse> OO (\<rightharpoondown>\<^sup>?\<lparr>\<omega>\<rparr>) OO L\<inverse>\<inverse> OO J | \<omega> I. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J})"
      using mutation_transition_std_is_type_correct
      by blast
    also have "\<dots> = (\<Squnion>J \<in> \<U>. \<Squnion> {I\<inverse>\<inverse> OO (\<rightharpoondown>\<^sup>?\<lparr>\<omega>\<rparr>) | \<omega> I. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J} OO L\<inverse>\<inverse> OO J)"
      by blast
    also have "\<dots> \<le> (\<Squnion>J \<in> \<U>. (\<rightharpoondown>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse> OO L\<inverse>\<inverse> OO J)"
      using connection
      by simp fast
    also have "\<dots> = (\<rightharpoondown>\<lparr>\<alpha>\<rparr>) OO (\<Squnion>J \<in> \<U>. J\<inverse>\<inverse> OO L\<inverse>\<inverse> OO J)"
      by blast
    also have "\<dots> = (\<rightharpoondown>\<lparr>\<alpha>\<rparr>) OO (\<Squnion>J \<in> \<U>. J\<inverse>\<inverse> OO L OO J)\<inverse>\<inverse>"
      by blast
    finally show ?thesis .
  qed
  then show ?thesis
    by simp
qed

lemma mutant_lifting_is_respectful [respectful]:
  shows "respectful \<M>"
proof -
  have "\<M> K \<leadsto> \<M> L" if "K \<leadsto> L" for K and L
  proof -
    from \<open>K \<leadsto> L\<close> have "K \<le> L" and "K\<inverse>\<inverse> \<le> L\<inverse>\<inverse>" and "K \<hookrightarrow> L" and "K\<inverse>\<inverse> \<hookrightarrow> L\<inverse>\<inverse>"
      by simp_all
    from \<open>K \<le> L\<close> have "\<M> K \<le> \<M> L"
      by auto
    moreover
    from \<open>K \<le> L\<close> and \<open>K \<hookrightarrow> L\<close> have "\<M> K \<hookrightarrow> \<M> L"
      by (fact unilateral_mutant_progression)
    moreover
    from \<open>K\<inverse>\<inverse> \<le> L\<inverse>\<inverse>\<close> and \<open>K\<inverse>\<inverse> \<hookrightarrow> L\<inverse>\<inverse>\<close> have "\<M> K\<inverse>\<inverse> \<hookrightarrow> \<M> L\<inverse>\<inverse>"
      by (fact unilateral_mutant_progression)
    then have "(\<M> K)\<inverse>\<inverse> \<hookrightarrow> (\<M> L)\<inverse>\<inverse>"
      unfolding mutant_lifting_def by blast
    ultimately show ?thesis
      by simp
  qed
  then show ?thesis
    by simp
qed

end

lemma mutation_is_compatible_with_bisimilarity:
  assumes "I \<in> \<U>" and "I s\<^sub>1 t\<^sub>1" and "I s\<^sub>2 t\<^sub>2" and "s\<^sub>1 \<sim> s\<^sub>2"
  shows "t\<^sub>1 \<sim> t\<^sub>2"
  using
    respectfully_transformed_bisimilarity_in_bisimilarity [OF mutant_lifting_is_respectful]
  and
    assms
  by auto

end

end
