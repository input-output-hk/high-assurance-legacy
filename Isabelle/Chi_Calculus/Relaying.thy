section \<open>Relaying of Data\<close>

theory Relaying
  imports Communication
begin

definition unidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<rightarrow>" 100) where
  "a \<rightarrow> b \<equiv> a \<triangleright>\<^sup>\<infinity> x. b \<triangleleft> x"

lemma early_multi_receive_redundancy:
  shows "a \<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma shortcut_redundancy:
  shows "a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c"
  using early_multi_receive_redundancy unfolding unidirectional_bridge_def .

lemma loop_redundancy_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a \<rightarrow> a \<approx>\<^sub>\<flat> \<currency>\<^sup>*a"
  sorry

definition bidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<leftrightarrow>" 100) where
  "a \<leftrightarrow> b \<equiv> a \<rightarrow> b \<parallel> b \<rightarrow> a"

lemma bidirectional_bridge_commutativity: "a \<leftrightarrow> b \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
  unfolding bidirectional_bridge_def using parallel_commutativity .

lemma forward_bridge_absorption: "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> (a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a"
    unfolding unidirectional_bridge_def and bidirectional_bridge_def
    using basic.bisimilarity_transitivity_rule and parallel_associativity parallel_commutativity
    by blast
  also have "(a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> a"
    unfolding unidirectional_bridge_def
    using multi_receive_idempotency and basic_parallel_preservation_left
    by simp
  finally show ?thesis
    unfolding bidirectional_bridge_def by blast
qed

lemma backward_bridge_absorption: "a \<leftrightarrow> b \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> b \<leftrightarrow> a \<parallel> b \<rightarrow> a"
    unfolding unidirectional_bridge_def and bidirectional_bridge_def
    using basic.bisimilarity_transitivity_rule and parallel_associativity parallel_commutativity
    by blast
  also have "b \<leftrightarrow> a \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
    by (simp add: forward_bridge_absorption)
  finally show ?thesis
    using basic.bisimilarity_transitivity_rule bidirectional_bridge_commutativity by blast
qed

lemma send_channel_switch:
  shows "a \<leftrightarrow> b \<parallel> a \<triangleleft> x \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> b \<triangleleft> x"
  sorry

lemma receive_channel_switch:
  shows "a \<leftrightarrow> b \<parallel> a \<triangleright> x. P x \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> b \<triangleright> x. P x"
  sorry

lemma multi_receive_channel_switch:
  shows "a \<leftrightarrow> b \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> b \<triangleright> x. P x"
  sorry

lemma source_switch:
  shows "a \<leftrightarrow> b \<parallel> a \<rightarrow> c \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> b \<rightarrow> c"
  sorry

lemma target_switch:
  shows "a \<leftrightarrow> b \<parallel> c \<rightarrow> a \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<rightarrow> b"
  sorry

lemma loss_switch:
  shows "a \<leftrightarrow> b \<parallel> \<currency>\<^sup>?a \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> \<currency>\<^sup>?b"
  sorry

lemma duplication_switch:
  shows "a \<leftrightarrow> b \<parallel> \<currency>\<^sup>+a \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> \<currency>\<^sup>+b"
  sorry

lemma duploss_switch:
  shows "a \<leftrightarrow> b \<parallel> \<currency>\<^sup>*a \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> \<currency>\<^sup>*b"
  sorry

lemma detour_squashing:
  shows "\<nu> b. (a \<leftrightarrow> b) \<approx>\<^sub>\<sharp> a \<rightarrow> a"
  sorry

lemma duploss_detour_collapse:
  shows "\<nu> b. (\<currency>\<^sup>*b \<parallel> a \<leftrightarrow> b) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a"
  sorry

definition distributor :: "[chan, chan list] \<Rightarrow> process" (infix "\<Rightarrow>" 100) where
  "a \<Rightarrow> bs \<equiv> a \<triangleright>\<^sup>\<infinity> x. \<Prod>b\<leftarrow>bs. b \<triangleleft> x"

lemma distributor_split:
  "\<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> bs \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> bs. a \<rightarrow> b"
  sorry

lemma sidetrack_redundancy:
  shows "\<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> (b\<^sub>0 # bs) \<parallel> a \<rightarrow> b\<^sub>0 \<approx>\<^sub>\<flat> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> (b\<^sub>0 # bs)"
  sorry

end
