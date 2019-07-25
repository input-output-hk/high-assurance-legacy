theory Equivalence
  imports Main "HOL-Eisbach.Eisbach_Tools"
begin

named_theorems equivalence_transfer and equivalence

method equivalence = (
  \<comment> \<open>Add the declared extra premises to the list of goal premises:\<close>
  insert equivalence,
  \<comment> \<open>Turn the chained facts into goal premises:\<close>
  insert TrueI,
  erule_tac TrueE,
  \<comment> \<open>Uncurry all conditional premises:\<close>
  ((match premises in prem [thin]: "_ \<Longrightarrow> _ \<Longrightarrow> _" (cut) \<Rightarrow> \<open>insert prem [uncurry]\<close>)+)?,
  \<comment> \<open>Relax the equivalence premises:\<close>
  (
    (
      match premises in
        inclusion [thin]: "\<X> \<le> \<Y>" (cut) for \<X> :: "['a, 'a] \<Rightarrow> bool" and \<Y> \<Rightarrow> \<open>
          \<comment> \<open>If the conclusion uses~\<^term>\<open>\<Y>\<close>, relax all equivalence premises that use~\<^term>\<open>\<X>\<close>:\<close>
          match conclusion in
            "\<Y> _ _" (cut) \<Rightarrow> \<open>
              match premises in
                equivalences [thin]: "\<X> _ _" (cut, multi) \<Rightarrow> \<open>
                  insert equivalences [THEN predicate2D [OF inclusion]]
                \<close> \<bar>
                _ (cut) \<Rightarrow> \<open>succeed\<close>,
              match premises in
                conditional_equivalences [thin]: "_ \<Longrightarrow> \<X> _ _" (cut, multi) \<Rightarrow> \<open>
                  insert conditional_equivalences [THEN predicate2D [OF inclusion]]
                \<close> \<bar>
                _ (cut) \<Rightarrow> \<open>succeed\<close>
            \<close> \<bar>
            _ (cut) \<Rightarrow> \<open>succeed\<close>
        \<close>
    )+
  )?,
  \<comment> \<open>Curry all conditional premises:\<close>
  ((match premises in prem [thin]: "_ &&& _ \<Longrightarrow> _" (cut) \<Rightarrow> \<open>insert prem [curry]\<close>)+)?,
  \<comment> \<open>Turn the equivalence premises into quotient type equalities:\<close>
  match premises in prems [thin]: _ (cut, multi) \<Rightarrow> \<open>insert prems [transferred]\<close>,
  \<comment> \<open>Try to solve the constructed goal:\<close>
  (
    \<comment> \<open>Turn the conclusion into a quotient type equality with process operations lifted:\<close>
    simp (no_asm) only: equivalence_transfer [THEN sym] id_def comp_def;
      \<comment> \<open>
        We need \<^theory_text>\<open>comp_def\<close> and perhaps \<^theory_text>\<open>id_def\<close>, because @{command lift_definition} creates facts
        involving \<^term>\<open>(\<circ>)\<close> and \<^const>\<open>id\<close>.
      \<close>
    \<comment> \<open>Simplify the remaining goal if one is left:\<close>
    simp (no_asm_simp)
    (* FIMXE:
      Document why simplification has to be done in two steps: in the case of \<open>\<Prod>\<close>, for example, we
      need to be sure that \<open>\<Prod>\<close> is turned into its lifted variant and not expanded.
    *)
  )
)

end
