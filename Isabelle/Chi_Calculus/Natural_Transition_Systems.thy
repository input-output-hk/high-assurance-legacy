section \<open>Transition Systems of the \<open>\<natural>\<close>-calculus\<close>

theory Natural_Transition_Systems
  imports Transition_Systems.Transition_Systems Processes
begin

(* FIXME:
  Every occurrence of “preservation” in this theory (including in comments) should be replaced by
  “compatibility” later.
*)

locale natural_transition_system =
  transition_system lift transition
    for lift :: "([process, process] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)" and transition +
  assumes receive_preservation:
    "\<And>a P Q. (\<And>x. P x \<sim> Q x) \<Longrightarrow> a \<triangleright> x. P x \<sim> a \<triangleright> x. Q x"
  assumes parallel_preservation:
    "\<And>p\<^sub>1 p\<^sub>2 q\<^sub>1 q\<^sub>2. \<lbrakk>p\<^sub>1 \<sim> p\<^sub>2; q\<^sub>1 \<sim>q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<sim> p\<^sub>2 \<parallel> q\<^sub>2"
  assumes new_channel_preservation:
    "\<And>P Q. (\<And>a. P a \<sim> Q a) \<Longrightarrow> \<nu> a. P a \<sim> \<nu> a. Q a"
begin

text \<open>
  The following two lemmas establish \<open>\<Prod>\<close>-preservation.
\<close>

lemma map_preservation:
  assumes "\<And>x. f x \<sim> g x"
  shows "list_all2 (\<sim>) (map f xs) (map g xs)"
  using assms by (induction xs) simp_all

lemma parallel_list_preservation:
  assumes "list_all2 (\<sim>) xs ys"
  shows "parallel_list xs \<sim> parallel_list ys"
  using assms and parallel_preservation
  by induction simp_all
  
end

end
