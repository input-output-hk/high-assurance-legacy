section \<open>Weak Transition Systems\<close>

theory "Transition_Systems-Weak_Transition_Systems"
imports
  "Transition_Systems-Transition_Systems"
begin

locale weak_transition_system =
  transition_system \<open>transition\<close>
  for transition :: "'a \<Rightarrow> 'p relation" (\<open>'(\<rightarrow>\<lparr>_\<rparr>')\<close>) +
  fixes silent :: 'a (\<open>\<tau>\<close>)
begin

subsection \<open>Weak Transitions\<close>

definition weak_transition :: "'a \<Rightarrow> 'p relation" (\<open>'(\<Rightarrow>\<lparr>_\<rparr>')\<close>) where
  [simp]: "(\<Rightarrow>\<lparr>\<alpha>\<rparr>) = (if \<alpha> = \<tau> then (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* else (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*)"

abbreviation weak_transition_std :: "'p \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> bool" (\<open>(_ \<Rightarrow>\<lparr>_\<rparr>/ _)\<close> [51, 0, 51] 50) where
  "p \<Rightarrow>\<lparr>\<alpha>\<rparr> q \<equiv> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) p q"

subsection \<open>The Weak System\<close>

sublocale weak: transition_system \<open>weak_transition\<close> .

notation weak.simulation (\<open>weak'_sim\<close>)
notation weak.bisimulation (\<open>weak'_bisim\<close>)
notation weak.bisimilarity (infix \<open>\<approx>\<close> 50)
notation weak.constant_bisimilarity (\<open>[\<approx>]\<close>)
notation weak.simulation_up_to (\<open>weak'_sim\<^bsub>_\<^esub>\<close>)
notation weak.bisimulation_up_to (\<open>weak'_bisim\<^bsub>_\<^esub>\<close>)

subsection \<open>The Mixed System\<close>

sublocale mixed: simulation_system \<open>transition\<close> \<open>weak_transition\<close> .

notation mixed.simulation (\<open>mixed'_sim\<close>)
notation mixed.bisimulation (\<open>mixed'_bisim\<close>)
notation mixed.bisimilarity (infix \<open>\<asymp>\<close> 50)
notation mixed.constant_bisimilarity (\<open>[\<asymp>]\<close>)
notation mixed.simulation_up_to (\<open>mixed'_sim\<^bsub>_\<^esub>\<close>)
notation mixed.bisimulation_up_to (\<open>mixed'_bisim\<^bsub>_\<^esub>\<close>)

subsection \<open>Relationships between the Weak and the Mixed System\<close>

context begin

private lemma mixed_simulation_is_multi_silent_simulation:
  assumes "mixed_sim K"
  shows "K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO K\<inverse>\<inverse>"
proof -
  have "K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^bsup>n\<^esup> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO K\<inverse>\<inverse>" for n
  proof (induction n)
    case 0
    show ?case by auto
  next
    case (Suc n)
    have "K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^bsup>Suc n\<^esup> = K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^bsup>n\<^esup> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)"
      by simp
    also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)"
      using Suc.IH by blast
    also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<Rightarrow>\<lparr>\<tau>\<rparr>) OO K\<inverse>\<inverse>"
      using \<open>mixed_sim K\<close> by blast
    also have "\<dots> = (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO K\<inverse>\<inverse>"
      by (auto intro: rtranclp_trans)
    finally show ?case .
  qed
  then show ?thesis
    unfolding rtranclp_is_Sup_relpowp
    by blast
qed

lemma weak_simulation_is_mixed_simulation_and_vice_versa:
  shows "weak_sim K \<longleftrightarrow> mixed_sim K"
proof
  assume "weak_sim K"
  have "K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO K\<inverse>\<inverse>" for \<alpha>
  proof -
    have "K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) \<le> K\<inverse>\<inverse> OO (\<Rightarrow>\<lparr>\<alpha>\<rparr>)"
      by auto
    also have "\<dots> \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO K\<inverse>\<inverse>"
      using \<open>weak_sim K\<close> by simp
    finally show ?thesis .
  qed
  then show "mixed_sim K"
    by simp
next
  assume "mixed_sim K"
  have "K\<inverse>\<inverse> OO (\<Rightarrow>\<lparr>\<alpha>\<rparr>) \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO K\<inverse>\<inverse>" for \<alpha>
  proof (cases "\<alpha> = \<tau>")
    case True
    then show ?thesis
      using mixed_simulation_is_multi_silent_simulation [OF \<open>mixed_sim K\<close>] by simp
  next
    case False
    from \<open>\<alpha> \<noteq> \<tau>\<close> have "K\<inverse>\<inverse> OO (\<Rightarrow>\<lparr>\<alpha>\<rparr>) = K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
      by simp
    also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
      using mixed_simulation_is_multi_silent_simulation [OF \<open>mixed_sim K\<close>] by blast
    also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
      using \<open>mixed_sim K\<close> by blast
    also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO K\<inverse>\<inverse>"
      using mixed_simulation_is_multi_silent_simulation [OF \<open>mixed_sim K\<close>] by blast
    also have "\<dots> = (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO K\<inverse>\<inverse>"
      using \<open>\<alpha> \<noteq> \<tau>\<close> by (simp, blast intro: rtranclp_trans)
    finally show ?thesis .
  qed
  then show "weak_sim K"
    by simp
qed

end

lemma weak_bisimulation_is_mixed_bisimulation_and_vice_versa:
  shows "weak_bisim K \<longleftrightarrow> mixed_bisim K"
  using weak_simulation_is_mixed_simulation_and_vice_versa
  by (simp del: conversep_conversep)

theorem weak_bisimilarity_is_mixed_bisimilarity:
  shows "(\<approx>) = (\<asymp>)"
proof -
  have "(\<approx>) = (GREATEST K. weak_bisim K)"
    using weak.bisimilarity_is_greatest_bisimulation .
  also have "\<dots> = (GREATEST K. mixed_bisim K)"
    by (simp only: weak_bisimulation_is_mixed_bisimulation_and_vice_versa)
  also have "\<dots> = (\<asymp>)"
    by (simp only: mixed.bisimilarity_is_greatest_bisimulation)
  finally show ?thesis .
qed

corollary mixed_bisimilarity_reflexivity_rule:
  shows "p \<asymp> p"
  using weak.bisimilarity_reflexivity_rule
  unfolding weak_bisimilarity_is_mixed_bisimilarity .

corollary mixed_bisimilarity_reflexivity:
  shows "reflp (\<asymp>)"
  using weak.bisimilarity_reflexivity
  unfolding weak_bisimilarity_is_mixed_bisimilarity .

corollary mixed_bisimilarity_transitivity_rule:
  assumes "p \<asymp> q" and "q \<asymp> r"
  shows "p \<asymp> r"
  using weak.bisimilarity_transitivity_rule and assms
  unfolding weak_bisimilarity_is_mixed_bisimilarity .

corollary mixed_bisimilarity_transitivity:
  shows "transp (\<asymp>)"
  using weak.bisimilarity_transitivity
  unfolding weak_bisimilarity_is_mixed_bisimilarity .

theorem mixed_bisimilarity_is_equivalence:
  shows "equivp (\<asymp>)"
  using
    mixed_bisimilarity_reflexivity
  and
    mixed.bisimilarity_symmetry
  and
    mixed_bisimilarity_transitivity
  by (fact equivpI)

subsection \<open>Relationships between the Normal and the Mixed System\<close>

lemma simulation_is_mixed_simulation:
  assumes "sim K"
  shows "mixed_sim K"
  using assms by (simp, blast)

lemma bisimulation_is_mixed_bisimulation:
  assumes "bisim K"
  shows "mixed_bisim K"
  using simulation_is_mixed_simulation and assms by blast

theorem bisimilarity_in_mixed_bisimilarity:
  shows "(\<sim>) \<le> (\<asymp>)"
proof -
  have "bisim (\<sim>)"
    using bisimilarity_is_bisimulation .
  then have "mixed_bisim (\<sim>)"
    by (fact bisimulation_is_mixed_bisimulation)
  then show "(\<sim>) \<le> (\<asymp>)"
    by (fact mixed.bisimulation_in_bisimilarity)
qed

subsection \<open>Relationships between the Normal and the Weak System\<close>

lemma simulation_is_weak_simulation:
  assumes "sim K"
  shows "weak_sim K"
  unfolding weak_simulation_is_mixed_simulation_and_vice_versa
  using simulation_is_mixed_simulation and assms .

lemma bisimulation_is_weak_bisimulation:
  assumes "bisim K"
  shows "weak_bisim K"
  unfolding weak_bisimulation_is_mixed_bisimulation_and_vice_versa
  using bisimulation_is_mixed_bisimulation and assms .

theorem bisimilarity_in_weak_bisimilarity:
  shows "(\<sim>) \<le> (\<approx>)"
  unfolding weak_bisimilarity_is_mixed_bisimilarity
  using bisimilarity_in_mixed_bisimilarity .

subsection \<open>Cleanup of notation\<close>

text \<open>
  We have no notation for the weak and mixed variants of the following relations and therefore
  remove their notation here in order to be able to use it later for their weak or mixed variants.

  We cannot do this cleanup right at the beginning, because surprisingly the notation for said
  relations is restored by the \<^theory_text>\<open>sublocale\<close> specifications for \<^theory_text>\<open>weak\<close> and \<^theory_text>\<open>mixed\<close>.
\<close>

no_notation unilateral_progression (infix "\<hookrightarrow>" 50)

no_notation bilateral_progression (infix "\<mapsto>" 50)

no_notation shortcut_progression (infix "\<leadsto>" 50)

subsection \<open>``Up to'' Methods\<close>

lemma pre_bisimilarity_chain_is_mixed_respectful [respectful]:
  assumes "mixed.respectful \<F>"
  shows "mixed.respectful ([\<sim>] \<frown> \<F>)"
proof -
  write mixed.unilateral_progression (infix "\<hookrightarrow>" 50)
  write mixed.shortcut_progression (infix "\<leadsto>" 50)
  have "([\<sim>] \<frown> \<F>) K \<leadsto> ([\<sim>] \<frown> \<F>) L" if "K \<leadsto> L" for K and L
  proof -
    from \<open>mixed.respectful \<F>\<close> and \<open>K \<leadsto> L\<close>
    have "\<F> K \<le> \<F> L" and "\<F> K \<hookrightarrow> \<F> L" and "(\<F> K)\<inverse>\<inverse> \<hookrightarrow> (\<F> L)\<inverse>\<inverse>"
      by simp_all
    have forward: "((\<sim>) OO \<F> K)\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO ((\<sim>) OO \<F> L)\<inverse>\<inverse>" for \<alpha>
    proof -
      have "((\<sim>) OO \<F> K)\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) = (\<F> K)\<inverse>\<inverse> OO (\<sim>)\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>)"
        by blast
      also have "\<dots> \<le> (\<F> K)\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<sim>)\<inverse>\<inverse>"
        using bisimilarity_is_simulation by blast
      also have "\<dots> \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<F> L)\<inverse>\<inverse> OO (\<sim>)\<inverse>\<inverse>"
        using \<open>\<F> K \<hookrightarrow> \<F> L\<close> by blast
      also have "\<dots> = (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO ((\<sim>) OO \<F> L)\<inverse>\<inverse>"
        by blast
      finally show ?thesis .
    qed
    have backward: "((\<sim>) OO \<F> K)\<inverse>\<inverse>\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO ((\<sim>) OO \<F> L)\<inverse>\<inverse>\<inverse>\<inverse>" for \<alpha>
    proof -
      have "((\<sim>) OO \<F> K)\<inverse>\<inverse>\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) = (\<sim>) OO \<F> K OO (\<rightarrow>\<lparr>\<alpha>\<rparr>)"
        by (simp add: relcompp_assoc)
      also have"\<dots> \<le> (\<sim>) OO (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO \<F> L"
        using \<open>(\<F> K)\<inverse>\<inverse> \<hookrightarrow> (\<F> L)\<inverse>\<inverse>\<close> by blast
      also have "\<dots> = (\<sim>)\<inverse>\<inverse> OO (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO \<F> L"
        by (blast intro: bisimilarity_symmetry_rule)
      also have "\<dots> \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<sim>)\<inverse>\<inverse> OO \<F> L"
        using bisimilarity_is_simulation [THEN simulation_is_weak_simulation]
        by blast
      also have "\<dots> = (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<sim>) OO \<F> L"
        by (blast intro: bisimilarity_symmetry_rule)
      also have "\<dots> = (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO ((\<sim>) OO \<F> L)\<inverse>\<inverse>\<inverse>\<inverse>"
        by simp
      finally show ?thesis .
    qed
    from \<open>\<F> K \<le> \<F> L\<close> and forward and backward show ?thesis
      by auto
  qed
  then show ?thesis
    by simp
qed

lemma post_bisimilarity_chain_is_mixed_respectful [respectful]:
  assumes "mixed.respectful \<F>"
  shows "mixed.respectful (\<F> \<frown> [\<sim>])"
proof -
  have "(\<F> \<frown> [\<sim>]) = ([\<sim>] \<frown> \<F>\<^sup>\<dagger>)\<^sup>\<dagger>"
    by (rule ext) (auto intro: bisimilarity_symmetry_rule)
  moreover from \<open>mixed.respectful \<F>\<close> have "mixed.respectful ([\<sim>] \<frown> \<F>\<^sup>\<dagger>)\<^sup>\<dagger>"
    by respectful
  ultimately show ?thesis
    by simp
qed

end

end
