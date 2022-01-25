section \<open>Weak Mutation Systems\<close>

theory "Transition_Systems-Weak_Mutation_Systems"
imports
  "Transition_Systems-Weak_Transition_Systems"
  "Transition_Systems-Mutation_Systems"
begin

locale weak_mutation_system =
  mutation_system
    \<open>transition\<close>
    \<open>transition\<close>
    \<open>shortcut_transition\<close>
    \<open>shortcut_transition\<close>
    \<open>\<U>\<close>
    \<open>mutation_transition_std\<close> +
  weak_transition_system \<open>transition\<close> \<open>\<tau>\<close>
  for
    transition :: "'a \<Rightarrow> 'p relation" (\<open>'(\<rightarrow>\<lparr>_\<rparr>')\<close>)
  and
    shortcut_transition :: "'a option \<Rightarrow> 'p relation" (\<open>'(\<rightarrow>\<^sup>?\<lparr>_\<rparr>')\<close>)
  and
    universe :: "'p relation set" (\<open>\<U>\<close>)
  and
    mutation_transition_std :: "'p relation \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> 'p relation \<Rightarrow> bool"
    (\<open>(_ \<longrightarrow>\<lparr>_ \<bar> _\<rparr>/ _)\<close> [51, 0, 0, 51] 50)
  and
    silent :: 'a (\<open>\<tau>\<close>)
  +
  assumes silent_compatibility:
    "\<forall>I \<in> \<U>. I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>) \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>) OO I\<inverse>\<inverse>"
  assumes silent_absorption:
    "\<And>\<alpha> I J. I \<longrightarrow>\<lparr>\<alpha> \<bar> Some \<tau>\<rparr> J \<Longrightarrow> I\<inverse>\<inverse> \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>"
begin

definition weak_shortcut_transition :: "'a option \<Rightarrow> 'p relation" (\<open>'(\<Rightarrow>\<^sup>?\<lparr>_\<rparr>')\<close>) where
  [simp]: "weak_shortcut_transition = with_shortcut weak_transition"

text \<open>
  We cannot make this lemma private and use it in the \<^theory_text>\<open>sublocale\<close> specification, because \<^theory_text>\<open>private\<close>
  can only appear under \<^theory_text>\<open>context\<close>, but \<^theory_text>\<open>sublocale\<close> is forbidden there.
\<close>

lemma multi_silent_compatibility:
  assumes "I \<in> \<U>"
  shows "I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO I\<inverse>\<inverse>"
proof -
  have "I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^bsup>n\<^esup> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO I\<inverse>\<inverse>" for n
  proof (induction n)
    case 0
    show ?case by auto
  next
    case (Suc n)
    have "I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^bsup>Suc n\<^esup> = I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^bsup>n\<^esup> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)"
      by simp
    also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)"
      using Suc.IH by blast
    also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<rightarrow>\<lparr>\<tau>\<rparr>) OO I\<inverse>\<inverse>"
      using silent_compatibility and \<open>I \<in> \<U>\<close>
      by blast
    also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO I\<inverse>\<inverse>"
      by (blast intro: rtranclp.rtrancl_into_rtrancl)
    finally show ?case .
  qed
  then show ?thesis
    unfolding rtranclp_is_Sup_relpowp
    by blast
qed

sublocale mixed:
  mutation_system
    \<open>transition\<close>
    \<open>weak_transition\<close>
    \<open>shortcut_transition\<close>
    \<open>weak_shortcut_transition\<close>
    \<open>\<U>\<close>
    \<open>mutation_transition_std\<close>
proof (unfold_locales, fold original_shortcut_transition_def weak_shortcut_transition_def)
  fix \<alpha>
  have "I\<inverse>\<inverse> OO (\<Rightarrow>\<^sup>?\<lparr>\<omega>\<rparr>) \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>" if "J \<in> \<U>" and "I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J" for \<omega> and I and J
  proof -
    from that have concrete_connection: "I\<inverse>\<inverse> OO (\<rightarrow>\<^sup>?\<lparr>\<omega>\<rparr>) \<le> (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>"
      using connection
      by blast
    from \<open>I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J\<close> have \<open>I \<in> \<U>\<close>
      using mutation_transition_std_is_type_correct
      by simp
    consider
      (shortcut)
        "\<omega> = None" |
      (silent)
        "\<omega> = Some \<tau>" |
      (observable)
        \<beta> where "\<beta> \<noteq> \<tau>" and "\<omega> = Some \<beta>"
      by blast
    then show ?thesis
    proof cases
      case shortcut
      have "I\<inverse>\<inverse> OO (\<Rightarrow>\<^sup>?\<lparr>None\<rparr>) = I\<inverse>\<inverse>"
        by auto
      also have "\<dots> = I\<inverse>\<inverse> OO (\<rightarrow>\<^sup>?\<lparr>None\<rparr>)"
        by auto
      also have "\<dots> \<le> (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>"
        using concrete_connection
        unfolding \<open>\<omega> = None\<close> .
      also have "\<dots> \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>"
        by auto
      finally show ?thesis
        unfolding \<open>\<omega> = None\<close> .
    next
      case silent
      have "I\<inverse>\<inverse> OO (\<Rightarrow>\<^sup>?\<lparr>Some \<tau>\<rparr>) = I\<inverse>\<inverse> OO (\<Rightarrow>\<lparr>\<tau>\<rparr>)"
        by simp
      also have "\<dots> = I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
        by simp
      also have "\<dots> \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
        using silent_absorption and \<open>I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J\<close>
        unfolding \<open>\<omega> = Some \<tau>\<close>
        by blast
      also have "\<dots> \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO J\<inverse>\<inverse>"
        using multi_silent_compatibility [OF \<open>J \<in> \<U>\<close>]
        by blast
      also have "\<dots> = (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>"
        by (simp, blast intro: rtranclp_trans)
      finally show ?thesis
        unfolding \<open>\<omega> = Some \<tau>\<close> .
    next
      case observable
      have "I\<inverse>\<inverse> OO (\<Rightarrow>\<^sup>?\<lparr>Some \<beta>\<rparr>) = I\<inverse>\<inverse> OO (\<Rightarrow>\<lparr>\<beta>\<rparr>)"
        by simp
      also have "\<dots> = I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<rightarrow>\<lparr>\<beta>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
        using \<open>\<beta> \<noteq> \<tau>\<close>
        by simp
      also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO I\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<beta>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
        using multi_silent_compatibility [OF \<open>I \<in> \<U>\<close>]
        by blast
      also have "\<dots> = (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO I\<inverse>\<inverse> OO (\<rightarrow>\<^sup>?\<lparr>Some \<beta>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
        by simp
      also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>*"
        using concrete_connection
        unfolding \<open>\<omega> = Some \<beta>\<close>
        by blast
      also have "\<dots> \<le> (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO (\<rightarrow>\<lparr>\<tau>\<rparr>)\<^sup>*\<^sup>* OO J\<inverse>\<inverse>"
        using multi_silent_compatibility [OF \<open>J \<in> \<U>\<close>]
        by blast
      also have "\<dots> \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>"
        by (auto intro: converse_rtranclp_into_rtranclp rtranclp_trans)
      finally show ?thesis
        unfolding \<open>\<omega> = Some \<beta>\<close> .
    qed
  qed
  then show "\<forall>J \<in> \<U>. \<Squnion> {I\<inverse>\<inverse> OO (\<Rightarrow>\<^sup>?\<lparr>\<omega>\<rparr>) | \<omega> I. I \<longrightarrow>\<lparr>\<alpha> \<bar> \<omega>\<rparr> J} \<le> (\<Rightarrow>\<lparr>\<alpha>\<rparr>) OO J\<inverse>\<inverse>"
    by blast
qed (fact mutation_transition_std_is_type_correct, fact dissection)

text \<open>
  The notation \<open>\<M>\<close> now stands for \<^const>\<open>mutant_lifting\<close> and \<^const>\<open>mixed.mutant_lifting\<close>. We drop
  it as a notation of \<^const>\<open>mutant_lifting\<close>, so that it becomes unique. The identifiers
  \<^const>\<open>mutant_lifting\<close> and \<^const>\<open>mixed.mutant_lifting\<close> refer to the same entity. We chose to keep
  \<open>\<M>\<close> as the notation for \<^const>\<open>mixed.mutant_lifting\<close>, since this is used in term output.
\<close>

no_notation mutant_lifting (\<open>\<M>\<close>)

end

end
