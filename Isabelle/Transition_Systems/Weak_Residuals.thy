section \<open>Weak Residuals\<close>

theory Weak_Residuals
  imports Residuals
begin

locale weak_residual =
  fixes silent :: "['process, 'residual] \<Rightarrow> bool"
  fixes absorb :: "(['process, 'residual] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)"
  assumes absorb_monotonicity [mono]:
    "\<I> \<le> \<J> \<Longrightarrow> absorb \<I> \<le> absorb \<J>"
  assumes left_neutrality:
    "silent OO absorb \<I> = \<I>"
  assumes right_neutrality:
    "absorb silent = (=)"
  assumes associativity:
    "absorb \<I> OO absorb \<J> = absorb (\<I> OO absorb \<J>)"
  assumes derived_lift_conversion_preservation:
    "absorb (\<X>\<inverse>\<inverse> OO silent) = (absorb (\<X> OO silent))\<inverse>\<inverse>"
begin

text \<open>
  Using \<open>absorb_monotonicity\<close>, we define a proof method for reasoning under \<^term>\<open>absorb\<close>. This
  method works analogously to \<open>under_lift\<close> and \<open>under_transfer\<close>.
\<close>

method under_absorb = (elim predicate2D [OF absorb_monotonicity, OF predicate2I, rotated])

abbreviation lift :: "(['process, 'process] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)" where
  "lift \<X> \<equiv> absorb (\<X> OO silent)"

sublocale residual lift
proof unfold_locales
  fix \<X> :: "['process, 'process] \<Rightarrow> bool" and \<Y>
  assume "\<X> \<le> \<Y>"
  then have "\<X> OO silent \<le> \<Y> OO silent"
    by (simp add: relcompp_mono)
  then show "absorb (\<X> OO silent) \<le> absorb (\<Y> OO silent)"
    by (fact absorb_monotonicity)
next
  show "absorb ((=) OO silent) = (=)"
    by (simp add: eq_OO right_neutrality)
next
  fix \<X> :: "['process, 'process] \<Rightarrow> bool" and \<Y>
  have "absorb ((\<X> OO \<Y>) OO silent) = absorb (\<X> OO (\<Y> OO silent))"
    by (simp add: relcompp_assoc)
  also have "\<dots> = absorb (\<X> OO (silent OO absorb (\<Y> OO silent)))"
    by (simp add: left_neutrality)
  also have "\<dots> = absorb ((\<X> OO silent) OO absorb (\<Y> OO silent))"
    by (simp add: relcompp_assoc)
  also have "\<dots> = absorb (\<X> OO silent) OO absorb (\<Y> OO silent)"
    by (simp add: associativity)
  finally show "absorb ((\<X> OO \<Y>) OO silent) = absorb (\<X> OO silent) OO absorb (\<Y> OO silent)" .
next
  fix \<X>
  show "absorb (\<X>\<inverse>\<inverse> OO silent) = (absorb (\<X> OO silent))\<inverse>\<inverse>"
    by (fact derived_lift_conversion_preservation)
qed

lemma silent_naturality: "\<X> OO silent = silent OO lift \<X>"
proof -
  show "\<X> OO silent = silent OO absorb (\<X> OO silent)"
    by (simp add: left_neutrality)
qed
lemma absorb_pre_naturality: "absorb (\<X> OO \<I>) = lift \<X> OO absorb \<I>"
proof -
  have "absorb (\<X> OO \<I>) = absorb (\<X> OO (silent OO absorb \<I>))"
    by (simp add: left_neutrality)
  also have "\<dots> = absorb ((\<X> OO silent) OO absorb \<I>)"
    by (simp add: relcompp_assoc)
  also have "\<dots> = absorb (\<X> OO silent) OO absorb \<I>"
    by (simp add: associativity)
  finally show ?thesis .
qed
lemma absorb_post_naturality: "absorb (\<I> OO lift \<Y>) = absorb \<I> OO lift \<Y>"
  by (simp add: associativity)
lemma absorb_naturality: "absorb (\<X> OO \<I> OO lift \<Y>) = lift \<X> OO absorb \<I> OO lift \<Y>"
  using absorb_pre_naturality and absorb_post_naturality
  by metis

end

end
