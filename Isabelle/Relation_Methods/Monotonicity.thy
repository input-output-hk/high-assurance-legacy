section \<open>Monotonicity\<close>

theory Monotonicity
  imports Main "HOL-Eisbach.Eisbach"
begin

text \<open>
  We define a proof method for reasoning under monotonic functions~\<open>\<F>\<close> that turn binary relations
  into binary relations. The invocation \<open>(under mono: monotonicity)\<close>, where \<open>monotonicity\<close> has the
  form \<^term>\<open>R \<le> S \<Longrightarrow> \<F> R \<le> \<F> S\<close>, expects a fact of the form \<^term>\<open>\<F> R y\<^sub>1 y\<^sub>2\<close> and a goal of the
  form \<^term>\<open>\<F> S y\<^sub>1 y\<^sub>2\<close> and generates the subgoal \<^term>\<open>\<And>x\<^sub>1 x\<^sub>2. R x\<^sub>1 x\<^sub>2 \<Longrightarrow> S x\<^sub>1 x\<^sub>2\<close>.
\<close>

method under uses mono = (elim predicate2D [OF mono, OF predicate2I, rotated])

end
