section \<open>Notions of Communication\<close>

theory Communication
  imports Core_Bisimilarities "HOL-Library.BNF_Corec"
begin

corec multi_receive :: "[chan, val \<Rightarrow> process] \<Rightarrow> process" where
  "multi_receive a P = a \<triangleright> x. (P x \<parallel> multi_receive a P)"
syntax
  "_multi_receive" :: "chan \<Rightarrow> pttrn \<Rightarrow> process \<Rightarrow> process"
  ("(3_ \<triangleright>\<^sup>\<infinity> _./ _)" [101, 0, 100] 100)
translations
  "a \<triangleright>\<^sup>\<infinity> x. p" \<rightleftharpoons> "CONST multi_receive a (\<lambda>x. p)"

(* FIXME:
  We should base the following on \<open>natural_transition_system\<close>, which would have to be extended with
  support for simulation up to context to be able to prove the compatibility law for \<open>\<triangleright>\<^sup>\<infinity>\<close>.
*)
context begin

private lift_definition basic :: "[chan, val \<Rightarrow> basic_behavior] \<Rightarrow> basic_behavior"
  is multi_receive
  sorry

private lift_definition basic_weak :: "[chan, val \<Rightarrow> basic_weak_behavior] \<Rightarrow> basic_weak_behavior"
  is multi_receive
  sorry

private lift_definition proper :: "[chan, val \<Rightarrow> proper_behavior] \<Rightarrow> proper_behavior"
  is multi_receive
  sorry

private lift_definition proper_weak :: "[chan, val \<Rightarrow> proper_weak_behavior] \<Rightarrow> proper_weak_behavior"
  is multi_receive
  sorry

lemmas [equivalence_transfer] =
  basic.abs_eq
  basic_weak.abs_eq
  proper.abs_eq
  proper_weak.abs_eq

end

text \<open>
  We extend \<^theory_text>\<open>natural_simps\<close> with rules for eliminating duplicates of \<open>\<triangleright>\<^sup>\<infinity>\<close>-processes, which are
  based on the observation that \<^const>\<open>multi_receive\<close> is idempotent.

  Incidentally, duplicate removal based on idempotence plays rather well with associativity and
  commutativity rules. The reason is the simplifier's handling of permutative rules, like
  commutativity: these rules are applied only when they lead to a smaller term, where ``smaller'' by
  default means ``lexicographically smaller'' (see Subsection~9.3.3 of the Isabelle/Isar Reference
  Manual). A result of this behavior is that equal processes in a chain of parallel compositions
  will sooner or later stand next to each other. If then a pair of equal processes stands at the end
  of the chain, it can be collapsed by applying an idempotency rule; if it does not stand at the
  end, it can be collapsed by a ``nested'' variant of an idempotency rule, analogous to the
  ``nested'' variant of commutativity.
\<close>
(* FIXME:
  Add a proper reference to the reference manual.
*)

lemma multi_receive_idempotency [natural_simps]: "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma multi_receive_nested_idempotency [natural_simps]:
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> q) \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> q"
proof -
  have "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> q) \<sim>\<^sub>\<flat> (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x) \<parallel> q"
    using parallel_associativity by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> q"
    using multi_receive_idempotency by equivalence
  finally show ?thesis .
qed

lemma context_localization:
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> b \<triangleright>\<^sup>\<infinity> x. Q x \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> b \<triangleright>\<^sup>\<infinity> x. (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> Q x)"
  sorry

abbreviation distributor :: "[chan, chan list] \<Rightarrow> process" (infix "\<Rightarrow>" 100) where
  "a \<Rightarrow> bs \<equiv> a \<triangleright>\<^sup>\<infinity> x. \<Prod>b\<leftarrow>bs. b \<triangleleft> x"

abbreviation loss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>?_" [1000] 1000) where
  "\<currency>\<^sup>?a \<equiv> a \<Rightarrow> []"

abbreviation duplication :: "chan \<Rightarrow> process" ("\<currency>\<^sup>+_" [1000] 1000) where
  "\<currency>\<^sup>+a \<equiv> a \<Rightarrow> [a, a]"

lemma multi_receive_split:
  assumes "\<And>x. P x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero>" and "\<And>x. Q x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero>"
  shows "\<currency>\<^sup>+a \<parallel> a \<triangleright>\<^sup>\<infinity> x. (P x \<parallel> Q x) \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

abbreviation duploss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>*_" [1000] 1000) where
  "\<currency>\<^sup>*a \<equiv> \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a"

lemma send_idempotency_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x \<approx>\<^sub>\<flat> \<currency>\<^sup>* a \<parallel> a \<triangleleft> x"
  sorry

abbreviation unidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<rightarrow>" 100) where
  "a \<rightarrow> b \<equiv> a \<Rightarrow> [b]"

lemma early_multi_receive_addition:
  shows "a \<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma shortcut_addition:
  shows "a \<rightarrow> b \<parallel> b \<rightarrow> c \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c"
  by (fact early_multi_receive_addition)

lemma loop_redundancy_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a \<rightarrow> a \<approx>\<^sub>\<flat> \<currency>\<^sup>*a"
  sorry

abbreviation bidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<leftrightarrow>" 100) where
  "a \<leftrightarrow> b \<equiv> a \<rightarrow> b \<parallel> b \<rightarrow> a"

lemma bidirectional_bridge_commutativity: "a \<leftrightarrow> b \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
  by (simp add: parallel_commutativity)

lemma forward_bridge_absorption: "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> (a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a"
    using basic.bisimilarity_transitivity_rule parallel_associativity parallel_commutativity by blast
  also have "(a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> a"
    using multi_receive_idempotency basic_parallel_preservation_left by blast
  finally show ?thesis
    by blast
qed

lemma backward_bridge_absorption: "a \<leftrightarrow> b \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> b \<leftrightarrow> a \<parallel> b \<rightarrow> a"
    using basic.bisimilarity_transitivity_rule parallel_associativity parallel_commutativity by blast
  also have "b \<leftrightarrow> a \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
    using forward_bridge_absorption .
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

lemma distributor_split:
  "\<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> bs \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> bs. a \<rightarrow> b"
  sorry

lemma sidetrack_addition:
  shows "\<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> (b\<^sub>0 # bs) \<approx>\<^sub>\<flat> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> (b\<^sub>0 # bs) \<parallel> a \<rightarrow> b\<^sub>0"
  sorry

end
