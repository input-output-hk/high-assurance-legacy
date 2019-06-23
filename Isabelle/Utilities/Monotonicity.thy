section \<open>Monotonicity\<close>

theory Monotonicity
  imports Main "HOL-Eisbach.Eisbach"
begin

text \<open>
  We define a proof method for reasoning under monotonic functions~\<open>f\<close> that turn binary relations
  into binary relations. The invocation \<open>(under mono: monotonicity)\<close>, where \<open>monotonicity\<close> has the
  form \<^term>\<open>\<X> \<le> \<Y> \<Longrightarrow> f \<X> \<le> f \<Y>\<close>, expects a fact of the form \<^term>\<open>f \<X> m\<^sub>1 m\<^sub>2\<close> and a goal of the
  form \<^term>\<open>f \<Y> m\<^sub>1 m\<^sub>2\<close> and generates the subgoal \<^term>\<open>\<And>n\<^sub>1 n\<^sub>2. \<X> n\<^sub>1 n\<^sub>2 \<Longrightarrow> \<Y> n\<^sub>1 n\<^sub>2\<close>.
\<close>

method under uses mono = (elim predicate2D [OF mono, OF predicate2I, rotated])

end
