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

end
