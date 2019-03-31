section \<open>Relaying Networks\<close>

theory Relaying
  imports Chi_Calculus.Communication
begin

abbreviation unidirectional_link :: "[chan, chan] \<Rightarrow> process" (infix "\<rightarrow>" 100) where
  "a \<rightarrow> b \<equiv> a \<triangleright>\<^sup>\<infinity> x. b \<triangleleft> x"

(* TODO: Prove it. *)
lemma unidirectional_link_idempotency: "a \<rightarrow> b \<parallel> a \<rightarrow> b \<approx>\<^sub>\<flat> a \<rightarrow> b" sorry

abbreviation bidirectional_link :: "[chan, chan] \<Rightarrow> process" (infix "\<leftrightarrow>" 100) where
  "a \<leftrightarrow> b \<equiv> a \<rightarrow> b \<parallel> b \<rightarrow> a"

(* TODO: Prove it. *)
lemma bidirectional_link_idempotency: "a \<leftrightarrow> b \<parallel> a \<leftrightarrow> b \<approx>\<^sub>\<flat> a \<leftrightarrow> b" sorry

lemma birectional_link_commutativity: "a \<leftrightarrow> b \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
  by (simp add: basic_parallel_commutativity)

lemma forward_link_absorption: "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> (a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a"
    using basic.bisimilarity_transitivity_rule basic_parallel_associativity basic_parallel_commutativity by blast
  also have "(a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> a"
    using multi_receive_idempotency basic_parallel_preservation_left by blast
  finally show ?thesis
    by blast
qed

lemma backward_link_absorption: "a \<leftrightarrow> b \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> b \<leftrightarrow> a \<parallel> b \<rightarrow> a"
    using basic.bisimilarity_transitivity_rule basic_parallel_associativity basic_parallel_commutativity by blast
  also have "b \<leftrightarrow> a \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
    by (simp add: forward_link_absorption)
  finally show ?thesis
    using basic.bisimilarity_transitivity_rule birectional_link_commutativity by blast
qed

lemma source_shift: "a \<leftrightarrow> b \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma dead_end_collapse: "\<nu> b. (\<currency>\<^sup>*b \<parallel> a \<leftrightarrow> b) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a"
  sorry
  (* NOTE: The \<open>\<currency>\<^sup>?b\<close>-part of \<open>\<currency>\<^sup>*b\<close> can be handled with \<open>source_shift\<close> *)

end
