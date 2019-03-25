section \<open>Diamond-Shaped Relaying Network\<close>

theory Diamond
  imports Relaying
begin

abbreviation diamond :: "[chan, chan, chan, chan, chan] \<Rightarrow> process" where
  "diamond a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<equiv>
    \<currency>\<^sup>*a\<^sub>0 \<parallel>
    \<nu> a\<^sub>1 a\<^sub>2 a\<^sub>3. (
      \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
      a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
      a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    )"

lemma diamond_collapse: "diamond a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a \<parallel> a \<rightarrow> b\<^sub>0 \<parallel> a \<rightarrow> b\<^sub>1 \<parallel> a \<rightarrow> b\<^sub>2 \<parallel> a \<rightarrow> b\<^sub>3"
  sorry

end
