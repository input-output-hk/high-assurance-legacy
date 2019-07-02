theory Equivalences
  imports Main "HOL-Eisbach.Eisbach"
begin

named_theorems equivalence and equivalence_simp and equivalence_cong

context begin

private lemma equivalence_rewrite_rule:
  assumes "equivp R"
  shows "R p q \<longleftrightarrow> R p = R q"
  using assms by (simp add: equivp_def)

method equivalence_simp = (
  simp
    only:
      equivalence [THEN equivalence_rewrite_rule]
      equivalence_simp [simplified equivalence [THEN equivalence_rewrite_rule]]
    cong:
      equivalence_cong [simplified equivalence [THEN equivalence_rewrite_rule]]
)

end

end
