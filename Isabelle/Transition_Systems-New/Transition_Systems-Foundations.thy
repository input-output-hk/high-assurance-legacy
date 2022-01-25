section \<open>Foundations\<close>

theory "Transition_Systems-Foundations"
imports
  Main
begin

subsection \<open>Repeated Composition\<close>

text \<open>
  This applies in particular to functions and relations.
\<close>

notation compower (\<open>(_\<^bsup>_\<^esup>)\<close> [1000, 0] 1000)

subsection \<open>Relations\<close>

type_synonym 'p relation = "'p \<Rightarrow> 'p \<Rightarrow> bool"

definition
  chain :: "
    ('p relation \<Rightarrow> 'p relation) \<Rightarrow>
    ('p relation \<Rightarrow> 'p relation) \<Rightarrow>
    ('p relation \<Rightarrow> 'p relation)"
  (infixr \<open>\<frown>\<close> 75)
where
  [simp]: "\<F> \<frown> \<G> = (\<lambda>K. \<F> K OO \<G> K)"

definition
  dual :: "('p relation \<Rightarrow> 'p relation) \<Rightarrow> ('p relation \<Rightarrow> 'p relation)"
  ("_\<^sup>\<dagger>" [1000] 1000)
where
  [simp]: "\<F>\<^sup>\<dagger> = (\<lambda>K. (\<F> K\<inverse>\<inverse>)\<inverse>\<inverse>)"

end
