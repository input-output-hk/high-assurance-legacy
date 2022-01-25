section \<open>Asynchronous Semantics\<close>

theory "Thorn_Calculus-Semantics-Asynchronous"
imports
  "Thorn_Calculus-Semantics-Synchronous"
begin

fun asynchronous_transition :: "action \<Rightarrow> process family relation" (\<open>'(\<rightarrow>\<^sub>a\<lparr>_\<rparr>')\<close>) where
  "(\<rightarrow>\<^sub>a\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr>) = {\<hole> \<guillemotleft> suffix n} OO {A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<hole>}" |
  "(\<rightarrow>\<^sub>a\<lparr>\<alpha>\<rparr>) = (\<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr>)"

abbreviation
  asynchronous_transition_std :: "process family \<Rightarrow> action \<Rightarrow> process family \<Rightarrow> bool"
  (\<open>(_ \<rightarrow>\<^sub>a\<lparr>_\<rparr>/ _)\<close> [51, 0, 51] 50)
where
  "P \<rightarrow>\<^sub>a\<lparr>\<alpha>\<rparr> Q \<equiv> (\<rightarrow>\<^sub>a\<lparr>\<alpha>\<rparr>) P Q"

end
