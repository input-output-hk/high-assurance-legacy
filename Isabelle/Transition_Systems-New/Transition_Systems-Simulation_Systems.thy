section \<open>Simulation Systems\<close>

theory "Transition_Systems-Simulation_Systems"
imports
  "Transition_Systems-Foundations"
  "HOL-Eisbach.Eisbach"
begin

unbundle lattice_syntax

locale simulation_system =
  fixes original_transition :: "'a \<Rightarrow> 'p relation" (\<open>'(\<rightharpoonup>\<lparr>_\<rparr>')\<close>)
  fixes simulating_transition :: "'a \<Rightarrow> 'p relation" (\<open>'(\<rightharpoondown>\<lparr>_\<rparr>')\<close>)
begin

abbreviation original_transition_std :: "'p \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> bool" (\<open>(_ \<rightharpoonup>\<lparr>_\<rparr>/ _)\<close> [51, 0, 51] 50) where
  "p \<rightharpoonup>\<lparr>\<alpha>\<rparr> q \<equiv> (\<rightharpoonup>\<lparr>\<alpha>\<rparr>) p q"
abbreviation simulating_transition_std :: "'p \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> bool" (\<open>(_ \<rightharpoondown>\<lparr>_\<rparr> _)\<close> [51, 0, 51] 50) where
  "p \<rightharpoondown>\<lparr>\<alpha>\<rparr> q \<equiv> (\<rightharpoondown>\<lparr>\<alpha>\<rparr>) p q"

subsection \<open>Simulations and Bisimulations\<close>

definition unilateral_progression :: "'p relation \<Rightarrow> 'p relation \<Rightarrow> bool" (infix \<open>\<hookrightarrow>\<close> 50) where
  [iff]: "K \<hookrightarrow> L \<longleftrightarrow> (\<forall>\<alpha>. K\<inverse>\<inverse> OO (\<rightharpoonup>\<lparr>\<alpha>\<rparr>) \<le> (\<rightharpoondown>\<lparr>\<alpha>\<rparr>) OO L\<inverse>\<inverse>)"

definition bilateral_progression :: "'p relation \<Rightarrow> 'p relation \<Rightarrow> bool" (infix \<open>\<mapsto>\<close> 50) where
  [iff]: "K \<mapsto> L \<longleftrightarrow> K \<hookrightarrow> L \<and> K\<inverse>\<inverse> \<hookrightarrow> L\<inverse>\<inverse>"

definition simulation :: "'p relation \<Rightarrow> bool" (\<open>sim\<close>) where
  [iff]: "sim K \<longleftrightarrow> K \<hookrightarrow> K"

definition bisimulation :: "'p relation \<Rightarrow> bool" (\<open>bisim\<close>) where
  [iff]: "bisim K \<longleftrightarrow> K \<mapsto> K"

subsection \<open>Bisimilarity\<close>

coinductive bisimilarity :: "'p relation" (infix \<open>\<sim>\<close> 50) where
  bisimilarity:
    "p \<sim> q"
    if
      "\<And>\<alpha> p'. p \<rightharpoonup>\<lparr>\<alpha>\<rparr> p' \<Longrightarrow> \<exists>q'. q \<rightharpoondown>\<lparr>\<alpha>\<rparr> q' \<and> p' \<sim> q'"
    and
      "\<And>\<alpha> q'. q \<rightharpoonup>\<lparr>\<alpha>\<rparr> q' \<Longrightarrow> \<exists>p'. p \<rightharpoondown>\<lparr>\<alpha>\<rparr> p' \<and> p' \<sim> q'"

lemma bisimilarity_symmetry_rule [sym]:
  assumes "p \<sim> q"
  shows "q \<sim> p"
  using assms by (coinduction arbitrary: p q) (simp, blast elim: bisimilarity.cases)

lemma bisimilarity_symmetry: "symp (\<sim>)"
  using bisimilarity_symmetry_rule ..

text \<open>
  The following two transitivity rules are useful for calculational reasoning with both equality and
  bisimilarity.
\<close>

lemma equality_bisimilarity_transitivity_rule [trans]:
  assumes "p = q" and "q \<sim> r"
  shows "p \<sim> r"
  using assms
  by simp

lemma bisimilarity_equality_transititity_rule [trans]:
  assumes "p \<sim> q" and "q = r"
  shows "p \<sim> r"
  using assms
  by simp

lemma bisimilarity_is_bisimulation:
  shows "bisim (\<sim>)"
  by (blast elim: bisimilarity.cases)

lemma bisimilarity_is_simulation:
  shows "sim (\<sim>)"
  using bisimilarity_is_bisimulation by simp

lemma bisimulation_in_bisimilarity:
  assumes "bisim K"
  shows "K \<le> (\<sim>)"
proof
  fix p and q
  assume "K p q"
  with \<open>bisim K\<close> show "p \<sim> q"
    by (coinduction arbitrary: p q) (simp, blast)
qed

theorem bisimilarity_is_greatest_bisimulation:
  shows "(\<sim>) = (GREATEST K. bisim K)"
  using bisimilarity_is_bisimulation and bisimulation_in_bisimilarity
  by (simp add: Greatest_equality)

subsection \<open>Respectful Functions\<close>

definition shortcut_progression :: "'p relation \<Rightarrow> 'p relation \<Rightarrow> bool" (infix \<open>\<leadsto>\<close> 50) where
  [simp]: "(\<leadsto>) = (\<le>) \<sqinter> (\<mapsto>)"

text \<open>
  We chose the term ``shortcut progression'', because \<open>(\<le>)\<close> is \<open>(\<mapsto>)\<close> for
  \<open>(\<rightharpoonup>)\<lparr>\<alpha>\<rparr> = (=) \<and> (\<rightharpoondown>)\<lparr>\<alpha>\<rparr> = (=)\<close> and we have \<open>(=) = (\<rightharpoonup>)\<lparr>\<alpha>\<rparr>\<^bsup>0\<^esup> \<and> (=) = (\<rightharpoondown>)\<lparr>\<alpha>\<rparr>\<^bsup>0\<^esup>\<close>. This is made
  formal in the following note.
\<close>

notepad begin
  interpret shortcut: simulation_system \<open>\<lambda>\<alpha>. (\<rightharpoonup>\<lparr>\<alpha>\<rparr>)\<^bsup>0\<^esup>\<close> \<open>\<lambda>\<alpha>. (\<rightharpoondown>\<lparr>\<alpha>\<rparr>)\<^bsup>0\<^esup>\<close> .
  have "shortcut.unilateral_progression = (\<le>)"
    unfolding shortcut.unilateral_progression_def
    by auto
  have "shortcut.bilateral_progression = (\<le>)"
    unfolding shortcut.unilateral_progression_def and shortcut.bilateral_progression_def
    by auto
end

lemma general_union_shortcut_progression:
  assumes "\<forall>K \<in> \<K>. \<exists>L \<in> \<L>. K \<leadsto> L"
  shows "\<Squnion> \<K> \<leadsto> \<Squnion> \<L>"
  using assms by (simp, fast)

definition respectful :: "('p relation \<Rightarrow> 'p relation) \<Rightarrow> bool" where
  [iff]: "respectful \<F> \<longleftrightarrow> (\<forall>K L. K \<leadsto> L \<longrightarrow> \<F> K \<leadsto> \<F> L)"

subsubsection \<open>Automatic Proof of Respectfulness\<close>

text \<open>
  We work with a single list of respectfulness facts anyhow. It would be weird to have this single
  fact list and the same \<^theory_text>\<open>respectful\<close> method based on it in each concrete interpretation. When
  invoking the method in the theory context, we would have to pick it from an interpretation, but
  which interpretation we chose would be arbitrary. Therefore we temporarily leave the locale
  context.
\<close>

end

named_theorems respectful

text \<open>
  Note that the \<^theory_text>\<open>respectful\<close> methods works also on conclusions that contain function
  variables~\<^term>\<open>\<F>\<close> if there are premises \<^term>\<open>respectful \<F>\<close>.
\<close>

method respectful = (intro respectful ballI | elim emptyE insertE | simp only:)+

context simulation_system begin

subsubsection \<open>Common Respectful Functions and Respectful Function Combinators\<close>

(*FIXME:
  Explain that we want \<open>\<bottom>\<close> for those cases where bisimilarity holds, because no transitions are
  possible at all.
*)

lemma bottom_is_respectful [respectful]:
  shows "respectful \<bottom>"
  by auto

definition constant_bisimilarity :: "'p relation \<Rightarrow> 'p relation" (\<open>[\<sim>]\<close>) where
  [simp]: "[\<sim>] = (\<lambda>_. (\<sim>))"

lemma constant_bisimilarity_is_respectful [respectful]:
  shows "respectful [\<sim>]"
  using bisimilarity_is_bisimulation by simp

lemma identity_is_respectful [respectful]:
  shows "respectful id"
  by simp

lemma function_composition_is_respectful [respectful]:
  assumes "respectful \<F>" and "respectful \<G>"
  shows "respectful (\<F> \<circ> \<G>)"
  using assms by simp

lemma general_union_is_respectful [respectful]:
  assumes "\<forall>\<F> \<in> \<FF>. respectful \<F>"
  shows "respectful (\<Squnion> \<FF>)"
proof -
  have "(\<Squnion> \<FF>) K \<leadsto> (\<Squnion> \<FF>) L" if "K \<leadsto> L" for K and L
  proof -
    from \<open>\<forall>\<F> \<in> \<FF>. respectful \<F>\<close> and \<open>K \<leadsto> L\<close> have "\<forall>\<F> \<in> \<FF>. \<F> K \<leadsto> \<F> L"
      by simp
    then have "\<forall>K' \<in> {\<F> K | \<F>. \<F> \<in> \<FF>}. \<exists>L' \<in> {\<F> L | \<F>. \<F> \<in> \<FF>}. K' \<leadsto> L'"
      by blast
    then have "\<Squnion> {\<F> K | \<F>. \<F> \<in> \<FF>} \<leadsto> \<Squnion> {\<F> L | \<F>. \<F> \<in> \<FF>}"
      by (fact general_union_shortcut_progression)
    moreover have "\<Squnion> {\<F> M | \<F>. \<F> \<in> \<FF>} = (\<Squnion> \<FF>) M" for M
      by auto
    ultimately show ?thesis
      by simp
  qed
  then show ?thesis by simp
qed

lemma union_is_respectful [respectful]:
  assumes "respectful \<F>" and "respectful \<G>"
  shows "respectful (\<F> \<squnion> \<G>)"
proof-
  from assms have "\<forall>\<H> \<in> {\<F>, \<G>}. respectful \<H>"
    by simp
  then have "respectful (\<Squnion> {\<F>, \<G>})"
    by (fact general_union_is_respectful)
  then show ?thesis
    by simp
qed

lemma dual_is_respectful [respectful]:
  assumes "respectful \<F>"
  shows "respectful \<F>\<^sup>\<dagger>"
  using assms by simp

subsubsection \<open>Respectfully Transformed Bisimilarity\<close>

theorem respectfully_transformed_bisimilarity_in_bisimilarity:
  assumes "respectful \<F>"
  shows "\<F> (\<sim>) \<le> (\<sim>)"
proof -
  from \<open>respectful \<F>\<close> have "bisim (\<F> (\<sim>))"
    using bisimilarity_is_bisimulation
    by simp
  then show ?thesis
    using bisimulation_in_bisimilarity
    by simp
qed

subsection \<open>``Up to'' Methods\<close>

definition simulation_up_to :: "('p relation \<Rightarrow> 'p relation) \<Rightarrow> 'p relation \<Rightarrow> bool" (\<open>sim\<^bsub>_\<^esub>\<close>) where
  [iff]: "sim\<^bsub>\<F>\<^esub> K \<longleftrightarrow> K \<hookrightarrow> \<F> K"

definition bisimulation_up_to :: "('p relation \<Rightarrow> 'p relation) \<Rightarrow> 'p relation \<Rightarrow> bool" (\<open>bisim\<^bsub>_\<^esub>\<close>) where
  [iff]: "bisim\<^bsub>\<F>\<^esub> K \<longleftrightarrow> K \<mapsto> \<F> K"

lemma simulation_up_to_identity_is_simulation_and_vice_versa:
  shows "sim\<^bsub>id\<^esub> K \<longleftrightarrow> sim K"
  by simp

lemma bisimulation_up_to_identity_is_bisimulation_and_vice_versa:
  shows "bisim\<^bsub>id\<^esub> K \<longleftrightarrow> bisim K"
  by simp

subsubsection \<open>Soundness\<close>

context begin

private definition
  expansion :: "('p relation \<Rightarrow> 'p relation) \<Rightarrow> ('p relation \<Rightarrow> 'p relation)"
  (\<open>(\<langle>_\<rangle>)\<close>)
where
  [simp]: "\<langle>\<F>\<rangle> = id \<squnion> \<F>"

private lemma expansion_is_respectful:
  assumes "respectful \<F>"
  shows "respectful \<langle>\<F>\<rangle>"
  unfolding expansion_def
  using identity_is_respectful and union_is_respectful and assms
  by iprover

private lemma bisimulation_from_bisimulation_up_to:
  assumes "respectful \<F>" and "bisim\<^bsub>\<F>\<^esub> K"
  shows "bisim (\<Squnion>n. \<langle>\<F>\<rangle>\<^bsup>n\<^esup> K)"
proof -
  have "\<langle>\<F>\<rangle>\<^bsup>n\<^esup> K \<leadsto> \<langle>\<F>\<rangle>\<^bsup>Suc n\<^esup> K" for n
  proof (induction n)
    case 0
    from \<open>bisim\<^bsub>\<F>\<^esub> K\<close> show ?case
      by (simp, blast)
  next
    case Suc
    with \<open>respectful \<F>\<close> show ?case
      using expansion_is_respectful
      by (simp del: shortcut_progression_def expansion_def)
  qed
  then have "\<forall>K' \<in> range (\<lambda>n. \<langle>\<F>\<rangle>\<^bsup>n\<^esup> K). \<exists>L' \<in> range (\<lambda>n. \<langle>\<F>\<rangle>\<^bsup>n\<^esup> K). K' \<leadsto> L'"
    by blast
  then have "(\<Squnion>n. \<langle>\<F>\<rangle>\<^bsup>n\<^esup> K) \<leadsto> (\<Squnion>n. \<langle>\<F>\<rangle>\<^bsup>n\<^esup> K)"
    by (fact general_union_shortcut_progression)
  then show ?thesis
    by simp
qed

theorem up_to_is_sound:
  assumes "respectful \<F>" and "bisim\<^bsub>\<F>\<^esub> K"
  shows "K \<le> (\<sim>)"
proof -
  from assms have "bisim (\<Squnion>n. \<langle>\<F>\<rangle>\<^bsup>n\<^esup> K)"
    by (fact bisimulation_from_bisimulation_up_to)
  then have "(\<Squnion>n. \<langle>\<F>\<rangle>\<^bsup>n\<^esup> K) \<le> (\<sim>)"
    by (fact bisimulation_in_bisimilarity)
  moreover have "K \<le> (\<Squnion>n. \<langle>\<F>\<rangle>\<^bsup>n\<^esup> K)"
    by (subst funpow_0 [of "\<langle>\<F>\<rangle>" K, symmetric], blast)
  ultimately show ?thesis
    by simp
qed

end

context begin

private lemma bisimulation_up_to_from_simulation_up_to:
  assumes "symp K" and "sim\<^bsub>\<F>\<^esub> K"
  shows "bisim\<^bsub>\<F> \<squnion> \<F>\<^sup>\<dagger>\<^esub> K"
proof -
  from \<open>symp K\<close> have "K\<inverse>\<inverse> = K"
    by (blast elim: sympE)
  with \<open>sim\<^bsub>\<F>\<^esub> K\<close> show ?thesis
    by auto
qed

theorem symmetric_up_to_is_sound:
  assumes "respectful \<F>" and "symp K" and "sim\<^bsub>\<F>\<^esub> K"
  shows "K \<le> (\<sim>)"
proof -
  from \<open>respectful \<F>\<close> have "respectful (\<F> \<squnion> \<F>\<^sup>\<dagger>)"
    by respectful
  moreover from \<open>symp K\<close> and \<open>sim\<^bsub>\<F>\<^esub> K\<close> have "bisim\<^bsub>\<F> \<squnion> \<F>\<^sup>\<dagger>\<^esub> K"
    by (fact bisimulation_up_to_from_simulation_up_to)
  ultimately show ?thesis
    by (fact up_to_is_sound)
qed

end

subsubsection \<open>Coinduction Rules\<close>

text \<open>
  The following corollaries are coinduction rules that correspond to the above soundness lemmas. To
  use an ``up to'' method, pick the corresponding rule, instantiate the variable~\<^term>\<open>\<F>\<close>
  appropriately, and pass the resulting fact to the \<^theory_text>\<open>coinduction\<close> method via a \<^theory_text>\<open>rule\<close>
  specification, along with an appropriate \<^theory_text>\<open>arbitrary\<close> specification. The \<^theory_text>\<open>coinduction\<close> method
  automatically derives the relation~\<^term>\<open>K\<close> from the goal and proves the assumption \<^term>\<open>K s t\<close>.
\<close>

corollary up_to_rule [case_names respectful forward_simulation backward_simulation]:
  assumes
    "K s t"
  and
    "respectful \<F>"
  and
    "\<And>\<alpha> s t s'. K s t \<Longrightarrow> s \<rightharpoonup>\<lparr>\<alpha>\<rparr> s' \<Longrightarrow> \<exists>t'. t \<rightharpoondown>\<lparr>\<alpha>\<rparr> t' \<and> \<F> K s' t'"
  and
    "\<And>\<alpha> s t t'. K s t \<Longrightarrow> t \<rightharpoonup>\<lparr>\<alpha>\<rparr> t' \<Longrightarrow> \<exists>s'. s \<rightharpoondown>\<lparr>\<alpha>\<rparr> s' \<and> \<F> K s' t'"
  shows "s \<sim> t"
  using up_to_is_sound [OF \<open>respectful \<F>\<close>, of K] and assms(1,3-4)
  by blast

corollary symmetric_up_to_rule [case_names respectful symmetry simulation]:
  assumes
    "K s t"
  and
    "respectful \<F>"
  and
    "\<And>s t. K s t \<Longrightarrow> K t s"
  and
    "\<And>\<alpha> s t s'. K s t \<Longrightarrow> s \<rightharpoonup>\<lparr>\<alpha>\<rparr> s' \<Longrightarrow> \<exists>t'. t \<rightharpoondown>\<lparr>\<alpha>\<rparr> t' \<and> \<F> K s' t'"
  shows "s \<sim> t"
  using symmetric_up_to_is_sound [OF \<open>respectful \<F>\<close>, of K] and assms (1,3-4)
  unfolding symp_def
  by blast

end

end
