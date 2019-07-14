theory Equivalences
  imports Main "HOL-Eisbach.Eisbach"
begin

named_theorems equivalence_transfer and equivalence

method equivalence = (
  \<comment> \<open>Add the declared extra premises to the list of goal premises:\<close>
  insert equivalence,
  \<comment> \<open>Turn the chained facts into goal premises:\<close>
  insert TrueI,
  erule_tac TrueE,
  \<comment> \<open>Relax the equivalence premises:\<close>
  (
    (
      match premises in
        inclusion [thin]: "\<X> \<le> \<Y>" for \<X> :: "['a, 'a] \<Rightarrow> bool" and \<Y> \<Rightarrow> \<open>
          \<comment> \<open>If the conclusion uses~\<^term>\<open>\<Y>\<close>, relax all equivalence premises that use~\<^term>\<open>\<X>\<close>:\<close>
          match conclusion in
            "\<Y> _ _" \<Rightarrow> \<open>
              match premises in
                equivalences [thin]: "\<X> _ _" (multi) \<Rightarrow> \<open>
                  insert equivalences [THEN predicate2D [OF inclusion]]
                \<close> \<bar>
                _ \<Rightarrow> \<open>succeed\<close>
            \<close> \<bar>
            _ \<Rightarrow> \<open>succeed\<close>
        \<close>
    )+
  )?,
  \<comment> \<open>Turn the equivalence premises into quotient type equalities:\<close>
  match premises in prems [thin]: _ (multi) \<Rightarrow> \<open>insert prems [transferred]\<close>,
  \<comment> \<open>Turn the conclusion into a quotient type equality and simplify it:\<close>
  simp (no_asm_simp) only: equivalence_transfer [THEN sym] id_def comp_def
    \<comment> \<open>
      We need \<^theory_text>\<open>comp_def\<close> and perhaps \<^theory_text>\<open>id_def\<close>, because @{command lift_definition} creates facts
      involving \<^term>\<open>(\<circ>)\<close> and \<^const>\<open>id\<close>.
    \<close>
)

end
