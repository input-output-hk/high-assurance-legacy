section \<open>Relaying of Data\<close>

theory Relaying
  imports Communication
begin

abbreviation unidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<rightarrow>" 100) where
  "a \<rightarrow> b \<equiv> a \<triangleright>\<^sup>\<infinity> x. b \<triangleleft> x"

(* TODO: Prove it. *)
lemma unidirectional_bridge_idempotency: "a \<rightarrow> b \<parallel> a \<rightarrow> b \<approx>\<^sub>\<flat> a \<rightarrow> b" sorry

lemma shortcut_addition:
  shows "a \<rightarrow> b \<parallel> b \<rightarrow> c \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c"
  sorry

lemma loop_redundancy_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a \<rightarrow> a \<approx>\<^sub>\<flat> \<currency>\<^sup>*a"
  sorry

abbreviation bidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<leftrightarrow>" 100) where
  "a \<leftrightarrow> b \<equiv> a \<rightarrow> b \<parallel> b \<rightarrow> a"

(* TODO: Prove it. *)
lemma bidirectional_bridge_idempotency: "a \<leftrightarrow> b \<parallel> a \<leftrightarrow> b \<approx>\<^sub>\<flat> a \<leftrightarrow> b" sorry

lemma birectional_bridge_commutativity: "a \<leftrightarrow> b \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
  by (simp add: basic_parallel_commutativity)

lemma forward_bridge_absorption: "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> (a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a"
    using basic.bisimilarity_transitivity_rule basic_parallel_associativity basic_parallel_commutativity by blast
  also have "(a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> a"
    using multi_receive_idempotency basic_parallel_preservation_left by blast
  finally show ?thesis
    by blast
qed

lemma backward_bridge_absorption: "a \<leftrightarrow> b \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> b \<leftrightarrow> a \<parallel> b \<rightarrow> a"
    using basic.bisimilarity_transitivity_rule basic_parallel_associativity basic_parallel_commutativity by blast
  also have "b \<leftrightarrow> a \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
    by (simp add: forward_bridge_absorption)
  finally show ?thesis
    using basic.bisimilarity_transitivity_rule birectional_bridge_commutativity by blast
qed

end
