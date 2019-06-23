section \<open>Weak Transition Systems\<close>

theory Weak_Transition_Systems
  imports Utilities.Utilities Transition_Systems Weak_Residuals
begin

locale weak_transition_system =
  weak_residual silent absorb for silent :: "['process, 'residual] \<Rightarrow> bool" and absorb +
  fixes strong_transition :: "['process, 'residual] \<Rightarrow> bool" (infix "\<rightarrow>" 50)
begin

sublocale strong: transition_system lift strong_transition
  by intro_locales

notation strong.pre_bisimilarity (infix "\<lesssim>" 50)
notation strong.bisimilarity (infix "\<sim>" 50)

inductive weak_transition :: "['process, 'residual] \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  strong_transition:
    "p \<rightarrow> c \<Longrightarrow> p \<Rightarrow> c" |
  silent_transition:
    "silent p c \<Longrightarrow> p \<Rightarrow> c" |
  composed_transition:
    "\<lbrakk>p \<Rightarrow> c; absorb (\<Rightarrow>) c d\<rbrakk> \<Longrightarrow> p \<Rightarrow> d"

sublocale weak: transition_system lift weak_transition
  by intro_locales

notation weak.pre_bisimilarity (infix "\<lessapprox>" 50)
notation weak.bisimilarity (infix "\<approx>" 50)

sublocale mixed: simulation_system lift strong_transition weak_transition
  by intro_locales

lemma weak_sim_equals_mixed_sim: "weak.sim = mixed.sim"
proof (intro ext, intro iffI)
  fix \<X>
  assume "\<X> \<le> weak.transfer \<X>" 
  also have "\<dots> \<le> mixed.transfer \<X>" by (blast intro: strong_transition)
  finally show "\<X> \<le> mixed.transfer \<X>" .
next
  fix \<X>
  assume "mixed.sim \<X>"
  show "weak.sim \<X>"
  proof weak.is_simulation_standard
    case (sim p q c)
    then show ?case
    proof (induction arbitrary: q)
      case (strong_transition p c q)
      with \<open>\<X> \<le> mixed.transfer \<X>\<close> show ?case by blast
    next
      case (silent_transition p c q)
      then have "(\<X>\<inverse>\<inverse> OO silent) q c"
        by blast
      then have "(silent OO lift \<X>\<inverse>\<inverse>) q c"
        using silent_naturality
        by simp
      then obtain d where "silent q d" and "lift \<X> c d"
        using lift_conversion_preservation
        by auto
      then show ?case
        by (blast intro: weak_transition.silent_transition)
    next
      case (composed_transition p c\<^sub>1 c' q)
      from composed_transition.IH(1) and \<open>\<X> p q\<close> obtain d\<^sub>1 where "q \<Rightarrow> d\<^sub>1" and "lift \<X> c\<^sub>1 d\<^sub>1"
        by blast
      let ?IH_2_core = "\<lambda>p\<^sub>1 c\<^sub>2. \<forall>q\<^sub>1. \<X> p\<^sub>1 q\<^sub>1 \<longrightarrow> (\<exists>d\<^sub>2. q\<^sub>1 \<Rightarrow> d\<^sub>2 \<and> lift \<X> c\<^sub>2 d\<^sub>2)"
      from composed_transition.IH(2) have "absorb ?IH_2_core c\<^sub>1 c'"
        by (under mono: absorb_monotonicity) (fact conjunct2)
      with \<open>lift \<X> c\<^sub>1 d\<^sub>1\<close> have "(lift \<X>\<inverse>\<inverse> OO absorb ?IH_2_core) d\<^sub>1 c'"
        by (auto simp add: lift_conversion_preservation)
      then have "absorb (\<X>\<inverse>\<inverse> OO ?IH_2_core) d\<^sub>1 c'"
        using absorb_pre_naturality
        by metis
      then have "absorb ((\<Rightarrow>) OO lift \<X>\<inverse>\<inverse>) d\<^sub>1 c'"
      proof (under mono: absorb_monotonicity)
        fix q\<^sub>1 and c\<^sub>2
        assume "(\<X>\<inverse>\<inverse> OO ?IH_2_core) q\<^sub>1 c\<^sub>2"
        then obtain p\<^sub>1 where "\<X> p\<^sub>1 q\<^sub>1" and "?IH_2_core p\<^sub>1 c\<^sub>2"
          by blast
        then obtain d\<^sub>2 where "q\<^sub>1 \<Rightarrow> d\<^sub>2" and "lift \<X> c\<^sub>2 d\<^sub>2"
          by blast
        then show "((\<Rightarrow>) OO lift \<X>\<inverse>\<inverse>) q\<^sub>1 c\<^sub>2"
          by (auto simp add: lift_conversion_preservation)
      qed
      then have "(absorb (\<Rightarrow>) OO lift \<X>\<inverse>\<inverse>) d\<^sub>1 c'"
        by (simp add: absorb_post_naturality)
      then obtain d' where "absorb (\<Rightarrow>) d\<^sub>1 d'" and "lift \<X> c' d'"
        by (auto simp add: lift_conversion_preservation)
      with \<open>q \<Rightarrow> d\<^sub>1\<close> show ?case
        by (blast intro: weak_transition.composed_transition)
    qed
  qed
qed
lemma weak_bisim_equals_mixed_bisim: "weak.bisim = mixed.bisim"
  by (simp add: fun_cong [OF weak_sim_equals_mixed_sim])
lemma weak_bisimilarity_equals_mixed_bisimilarity: "weak.bisimilarity = mixed.bisimilarity"
proof -
  have "weak.bisimilarity = (GREATEST \<X>. weak.bisim \<X>)"
    by (fact weak.bisimilarity_is_greatest_bisimulation)
  also have "\<dots> = (GREATEST \<X>. mixed.bisim \<X>)"
    by (simp add: weak_bisim_equals_mixed_bisim)
  also have "\<dots> = mixed.bisimilarity"
    by (simp add: mixed.bisimilarity_is_greatest_bisimulation)
  finally show ?thesis .
qed
lemma strong_simulation_is_weak_simulation: "strong.sim \<X> \<Longrightarrow> weak.sim \<X>"
proof -
  assume "\<X> \<le> strong.transfer \<X>"
  also have "\<dots> \<le> mixed.transfer \<X>" by (blast intro: strong_transition)
  finally have "mixed.sim \<X>" .
  then show "weak.sim \<X>" by (simp add: fun_cong [OF weak_sim_equals_mixed_sim])
qed
lemma strong_bisimulation_is_weak_bisimulation: "strong.bisim \<X> \<Longrightarrow> weak.bisim \<X>"
  using strong_simulation_is_weak_simulation by blast
lemma strong_bisimilarity_in_weak_bisimilarity: "(\<sim>) \<le> (\<approx>)"
proof -
  have "strong.bisim (\<sim>)" by (fact strong.bisimilarity_is_bisimulation)
  then have "weak.bisim (\<sim>)" by (fact strong_bisimulation_is_weak_bisimulation)
  then show "(\<sim>) \<le> (\<approx>)" by (fact weak.bisimulation_in_bisimilarity)
qed

end

end
