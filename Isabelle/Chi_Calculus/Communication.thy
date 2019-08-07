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

private lift_definition
  basic_multi_receive :: "[chan, val \<Rightarrow> basic_behavior] \<Rightarrow> basic_behavior"
  is multi_receive
  sorry

private lift_definition
  basic_weak_multi_receive :: "[chan, val \<Rightarrow> basic_weak_behavior] \<Rightarrow> basic_weak_behavior"
  is multi_receive
  sorry

private lift_definition
  proper_multi_receive :: "[chan, val \<Rightarrow> proper_behavior] \<Rightarrow> proper_behavior"
  is multi_receive
  sorry

private lift_definition
  proper_weak_multi_receive :: "[chan, val \<Rightarrow> proper_weak_behavior] \<Rightarrow> proper_weak_behavior"
  is multi_receive
  sorry

lemmas [equivalence_transfer] =
  basic_multi_receive.abs_eq
  basic_weak_multi_receive.abs_eq
  proper_multi_receive.abs_eq
  proper_weak_multi_receive.abs_eq

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

lemma inner_multi_receive_redundancy:
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> b \<triangleright>\<^sup>\<infinity> x. (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> Q x) \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> b \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

definition distributor :: "[chan, chan list] \<Rightarrow> process" (infix "\<Rightarrow>" 100) where
  "a \<Rightarrow> bs \<equiv> a \<triangleright>\<^sup>\<infinity> x. \<Prod>b\<leftarrow>bs. b \<triangleleft> x"

context begin

private lift_definition basic_distributor :: "[chan, chan list] \<Rightarrow> basic_behavior"
  is distributor
  sorry

private lift_definition basic_weak_distributor :: "[chan, chan list] \<Rightarrow> basic_weak_behavior"
  is distributor
  sorry

private lift_definition proper_distributor :: "[chan, chan list] \<Rightarrow> proper_behavior"
  is distributor
  sorry

private lift_definition proper_weak_distributor :: "[chan, chan list] \<Rightarrow> proper_weak_behavior"
  is distributor
  sorry

lemmas [equivalence_transfer] =
  basic_distributor.abs_eq
  basic_weak_distributor.abs_eq
  proper_distributor.abs_eq
  proper_weak_distributor.abs_eq

end

lemma distributor_idempotency [natural_simps]:
  shows "a \<Rightarrow> bs \<parallel> a \<Rightarrow> bs \<sim>\<^sub>\<flat> a \<Rightarrow> bs"
  unfolding distributor_def using multi_receive_idempotency .

lemma distributor_nested_idempotency [natural_simps]:
  shows "a \<Rightarrow> bs \<parallel> (a \<Rightarrow> bs \<parallel> p) \<sim>\<^sub>\<flat> a \<Rightarrow> bs \<parallel> p"
  unfolding distributor_def using multi_receive_nested_idempotency .

definition loss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>?_" [1000] 1000) where
  "\<currency>\<^sup>?a \<equiv> a \<Rightarrow> []"

context begin

private lift_definition basic_loss :: "chan \<Rightarrow> basic_behavior"
  is loss
  sorry

private lift_definition basic_weak_loss :: "chan \<Rightarrow> basic_weak_behavior"
  is loss
  sorry

private lift_definition proper_loss :: "chan \<Rightarrow> proper_behavior"
  is loss
  sorry

private lift_definition proper_weak_loss :: "chan \<Rightarrow> proper_weak_behavior"
  is loss
  sorry

lemmas [equivalence_transfer] =
  basic_loss.abs_eq
  basic_weak_loss.abs_eq
  proper_loss.abs_eq
  proper_weak_loss.abs_eq

end

lemma loss_idempotency [natural_simps]:
  shows "\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>?a \<sim>\<^sub>\<flat> \<currency>\<^sup>?a"
  unfolding loss_def using distributor_idempotency .

lemma loss_nested_idempotency [natural_simps]:
  shows "\<currency>\<^sup>?a \<parallel> (\<currency>\<^sup>?a \<parallel> p) \<sim>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> p"
  unfolding loss_def using distributor_nested_idempotency .

definition duplication :: "chan \<Rightarrow> process" ("\<currency>\<^sup>+_" [1000] 1000) where
  "\<currency>\<^sup>+a \<equiv> a \<Rightarrow> [a, a]"

context begin

private lift_definition basic_duplication :: "chan \<Rightarrow> basic_behavior"
  is duplication
  sorry

private lift_definition basic_weak_duplication :: "chan \<Rightarrow> basic_weak_behavior"
  is duplication
  sorry

private lift_definition proper_duplication :: "chan \<Rightarrow> proper_behavior"
  is duplication
  sorry

private lift_definition proper_weak_duplication :: "chan \<Rightarrow> proper_weak_behavior"
  is duplication
  sorry

lemmas [equivalence_transfer] =
  basic_duplication.abs_eq
  basic_weak_duplication.abs_eq
  proper_duplication.abs_eq
  proper_weak_duplication.abs_eq

end

lemma duplication_idempotency [natural_simps]:
  shows "\<currency>\<^sup>+a \<parallel> \<currency>\<^sup>+a \<sim>\<^sub>\<flat> \<currency>\<^sup>+a"
  unfolding duplication_def using distributor_idempotency .

lemma duplication_nested_idempotency [natural_simps]:
  shows "\<currency>\<^sup>+a \<parallel> (\<currency>\<^sup>+a \<parallel> p) \<sim>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> p"
  unfolding duplication_def using distributor_nested_idempotency .

lemma multi_receive_split:
  assumes "\<And>x. P x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero>" and "\<And>x. Q x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero>"
  shows "\<currency>\<^sup>+a \<parallel> a \<triangleright>\<^sup>\<infinity> x. (P x \<parallel> Q x) \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

definition duploss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>*_" [1000] 1000) where
  "\<currency>\<^sup>*a \<equiv> \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a"

context begin

private lift_definition basic_duploss :: "chan \<Rightarrow> basic_behavior"
  is duploss
  sorry

private lift_definition basic_weak_duploss :: "chan \<Rightarrow> basic_weak_behavior"
  is duploss
  sorry

private lift_definition proper_duploss :: "chan \<Rightarrow> proper_behavior"
  is duploss
  sorry

private lift_definition proper_weak_duploss :: "chan \<Rightarrow> proper_weak_behavior"
  is duploss
  sorry

lemmas [equivalence_transfer] =
  basic_duploss.abs_eq
  basic_weak_duploss.abs_eq
  proper_duploss.abs_eq
  proper_weak_duploss.abs_eq

end

lemma duploss_idempotency [natural_simps]:
  shows "\<currency>\<^sup>*a \<parallel> \<currency>\<^sup>*a \<sim>\<^sub>\<flat> \<currency>\<^sup>*a"
  unfolding duploss_def using natural_simps by equivalence

lemma duploss_nested_idempotency [natural_simps]:
  shows "\<currency>\<^sup>*a \<parallel> (\<currency>\<^sup>*a \<parallel> p) \<sim>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> p"
  unfolding duploss_def using natural_simps by equivalence

lemma send_idempotency_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x \<approx>\<^sub>\<flat> \<currency>\<^sup>* a \<parallel> a \<triangleleft> x"
  sorry

definition unidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<rightarrow>" 100) where
  "a \<rightarrow> b \<equiv> a \<Rightarrow> [b]"

context begin

private lift_definition basic_unidirectional_bridge :: "[chan, chan] \<Rightarrow> basic_behavior"
  is unidirectional_bridge
  sorry

private lift_definition basic_weak_unidirectional_bridge :: "[chan, chan] \<Rightarrow> basic_weak_behavior"
  is unidirectional_bridge
  sorry

private lift_definition proper_unidirectional_bridge :: "[chan, chan] \<Rightarrow> proper_behavior"
  is unidirectional_bridge
  sorry

private lift_definition proper_weak_unidirectional_bridge :: "[chan, chan] \<Rightarrow> proper_weak_behavior"
  is unidirectional_bridge
  sorry

lemmas [equivalence_transfer] =
  basic_unidirectional_bridge.abs_eq
  basic_weak_unidirectional_bridge.abs_eq
  proper_unidirectional_bridge.abs_eq
  proper_weak_unidirectional_bridge.abs_eq

end

lemma unidirectional_bridge_idempotency [natural_simps]:
  shows "a \<rightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> a \<rightarrow> b"
  unfolding unidirectional_bridge_def using distributor_idempotency .

lemma unidirectional_bridge_nested_idempotency [natural_simps]:
  shows "a \<rightarrow> b \<parallel> (a \<rightarrow> b \<parallel> p) \<sim>\<^sub>\<flat> a \<rightarrow> b \<parallel> p"
  unfolding unidirectional_bridge_def using distributor_nested_idempotency .

lemma early_multi_receive_redundancy:
  shows "a \<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma shortcut_redundancy:
  shows "a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c"
  using early_multi_receive_redundancy unfolding unidirectional_bridge_def and distributor_def .

lemma loop_redundancy_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a \<rightarrow> a \<approx>\<^sub>\<flat> \<currency>\<^sup>*a"
  sorry

definition bidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<leftrightarrow>" 100) where
  "a \<leftrightarrow> b \<equiv> a \<rightarrow> b \<parallel> b \<rightarrow> a"

context begin

private lift_definition basic_bidirectional_bridge :: "[chan, chan] \<Rightarrow> basic_behavior"
  is bidirectional_bridge
  sorry

private lift_definition basic_weak_bidirectional_bridge :: "[chan, chan] \<Rightarrow> basic_weak_behavior"
  is bidirectional_bridge
  sorry

private lift_definition proper_bidirectional_bridge :: "[chan, chan] \<Rightarrow> proper_behavior"
  is bidirectional_bridge
  sorry

private lift_definition proper_weak_bidirectional_bridge :: "[chan, chan] \<Rightarrow> proper_weak_behavior"
  is bidirectional_bridge
  sorry

lemmas [equivalence_transfer] =
  basic_bidirectional_bridge.abs_eq
  basic_weak_bidirectional_bridge.abs_eq
  proper_bidirectional_bridge.abs_eq
  proper_weak_bidirectional_bridge.abs_eq

end

lemma bidirectional_bridge_idempotency [natural_simps]:
  shows "a \<leftrightarrow> b \<parallel> a \<leftrightarrow> b \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
  unfolding bidirectional_bridge_def using natural_simps by equivalence

lemma bidirectional_bridge_nested_idempotency [natural_simps]:
  shows "a \<leftrightarrow> b \<parallel> (a \<leftrightarrow> b \<parallel> p) \<sim>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> p"
  unfolding bidirectional_bridge_def using natural_simps by equivalence

lemma bidirectional_bridge_commutativity: "a \<leftrightarrow> b \<sim>\<^sub>\<flat> b \<leftrightarrow> a"
  unfolding bidirectional_bridge_def using parallel_commutativity .

lemma forward_bridge_absorption: "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> a \<leftrightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> a \<rightarrow> b \<sim>\<^sub>\<flat> (a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a"
    unfolding unidirectional_bridge_def and bidirectional_bridge_def
    using basic.bisimilarity_transitivity_rule and parallel_associativity parallel_commutativity
    by blast
  also have "(a \<rightarrow> b \<parallel> a \<rightarrow> b) \<parallel> b \<rightarrow> a \<sim>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> a"
    using multi_receive_idempotency and basic_parallel_preservation_left
    unfolding unidirectional_bridge_def and distributor_def
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

lemma distributor_split:
  "\<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> bs \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> bs. a \<rightarrow> b"
  sorry

lemma sidetrack_redundancy:
  shows "\<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> (b\<^sub>0 # bs) \<parallel> a \<rightarrow> b\<^sub>0 \<approx>\<^sub>\<flat> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> (b\<^sub>0 # bs)"
  sorry

end
