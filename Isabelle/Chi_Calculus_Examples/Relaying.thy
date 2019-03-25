section \<open>Relaying networks\<close>

theory Relaying
  imports Chi_Calculus.Communication
begin

abbreviation unidirectional_link :: "[chan, chan] \<Rightarrow> process" (infix "\<rightarrow>" 100) where
  "a \<rightarrow> b \<equiv> a \<triangleright>\<^sup>\<infinity> x. b \<triangleleft> x"

abbreviation bidirectional_link :: "[chan, chan] \<Rightarrow> process" (infix "\<leftrightarrow>" 100) where
  "a \<leftrightarrow> b \<equiv> a \<rightarrow> b \<parallel> b \<rightarrow> a"

lemma source_shift: "a \<leftrightarrow> b \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma dead_end_collapse: "\<nu> b. (\<currency>\<^sup>*b \<parallel> a \<leftrightarrow> b) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a"
  sorry

end
