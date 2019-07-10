section \<open>Notions of Communication\<close>

theory Communication
  imports Proper_Weak_Transition_System "HOL-Library.BNF_Corec"
begin

corec multi_receive :: "[chan, val \<Rightarrow> process] \<Rightarrow> process" where
  "multi_receive a P = a \<triangleright> x. (P x \<parallel> multi_receive a P)"
syntax
  "_multi_receive" :: "chan \<Rightarrow> pttrn \<Rightarrow> process \<Rightarrow> process"
  ("(3_ \<triangleright>\<^sup>\<infinity> _./ _)" [101, 0, 100] 100)
translations
  "a \<triangleright>\<^sup>\<infinity> x. p" \<rightleftharpoons> "CONST multi_receive a (\<lambda>x. p)"

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

lemmas [equivalence_simp_goal_preparation] =
  basic.abs_eq
  basic_weak.abs_eq
  proper.abs_eq
  proper_weak.abs_eq

end

lemma multi_receive_idempotency: "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma context_localization:
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> b \<triangleright>\<^sup>\<infinity> x. Q x \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> b \<triangleright>\<^sup>\<infinity> x. (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> Q x)"
  sorry

abbreviation loss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>?_" [1000] 1000) where
  "\<currency>\<^sup>?a \<equiv> a \<triangleright>\<^sup>\<infinity> _. \<zero>"

lemma loss_idempotency: "\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>?a \<sim>\<^sub>\<flat> \<currency>\<^sup>?a"
  by (fact multi_receive_idempotency)

abbreviation duplication :: "chan \<Rightarrow> process" ("\<currency>\<^sup>+_" [1000] 1000) where
  "\<currency>\<^sup>+a \<equiv> a \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x)"

lemma duplication_idempotency: "\<currency>\<^sup>+a \<parallel> \<currency>\<^sup>+a \<sim>\<^sub>\<flat> \<currency>\<^sup>+a"
  by (fact multi_receive_idempotency)

lemma multi_receive_split:
  assumes "\<And>x. P x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero>" and "\<And>x. Q x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero>"
  shows "\<currency>\<^sup>+a \<parallel> a \<triangleright>\<^sup>\<infinity> x. (P x \<parallel> Q x) \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

abbreviation duploss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>*_" [1000] 1000) where
  "\<currency>\<^sup>*a \<equiv> \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a"

lemma duploss_idempotency: "\<currency>\<^sup>*a \<parallel> \<currency>\<^sup>*a \<sim>\<^sub>\<flat> \<currency>\<^sup>*a"
  sorry

lemma send_idempotency_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x \<approx>\<^sub>\<flat> \<currency>\<^sup>* a \<parallel> a \<triangleleft> x"
  sorry

end
