section \<open>Standard Weak Residuals\<close>

theory Std_Weak_Residuals
  imports Weak_Residuals
begin

locale std_weak_residual =
  residual lift for lift :: "(['process, 'process] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)" +
  fixes silent :: "['process, 'residual] \<Rightarrow> bool"
  assumes silent_left_uniqueness_and_left_totality:
    "silent OO silent\<inverse>\<inverse> = (=)"
  assumes silent_right_uniqueness:
    "silent\<inverse>\<inverse> OO silent \<le> (=)"
  assumes std_silent_naturality:
    "\<X> OO silent = silent OO lift \<X>"
begin

lemma silent_converse_naturality: "silent\<inverse>\<inverse> OO \<X> = lift \<X> OO silent\<inverse>\<inverse>"
proof -
  have "silent\<inverse>\<inverse> OO \<X> = (\<X>\<inverse>\<inverse> OO silent)\<inverse>\<inverse>"
    by (simp add: converse_relcompp)
  also have "\<dots> = (silent OO lift \<X>\<inverse>\<inverse>)\<inverse>\<inverse>"
    by (simp add: std_silent_naturality)
  also have "\<dots> = (silent OO (lift \<X>)\<inverse>\<inverse>)\<inverse>\<inverse>"
    by (simp add: lift_conversion_preservation)
  also have "\<dots> = lift \<X> OO silent\<inverse>\<inverse>"
    by (simp add: converse_relcompp)
  finally show ?thesis .
qed

abbreviation
  absorb_downward :: "(['process, 'residual] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)"
where
  "absorb_downward \<I> \<equiv> silent\<inverse>\<inverse> OO \<I>"

lemma absorb_downward_monotonicity: "\<I> \<le> \<J> \<Longrightarrow> absorb_downward \<I> \<le> absorb_downward \<J>"
  by (simp add: relcompp_mono)

abbreviation
  absorb_upward :: "(['process, 'residual] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)"
where
  "absorb_upward \<I> \<equiv> lift (\<I> OO silent\<inverse>\<inverse>)"

lemma absorb_upward_monotonicity: "\<I> \<le> \<J> \<Longrightarrow> absorb_upward \<I> \<le> absorb_upward \<J>"
  by (simp add: relcompp_mono lift_monotonicity)

lemma deterministic_smashing_equality: "absorb_upward \<I> OO silent\<inverse>\<inverse> = absorb_downward \<I> OO silent\<inverse>\<inverse>"
proof -
  have "lift (\<I> OO silent\<inverse>\<inverse>) OO silent\<inverse>\<inverse> = silent\<inverse>\<inverse> OO (\<I> OO silent\<inverse>\<inverse>)"
    by (simp add: silent_converse_naturality)
  also have "\<dots> = (silent\<inverse>\<inverse> OO \<I>) OO silent\<inverse>\<inverse>"
    by (simp add: relcompp_assoc)
  finally show ?thesis .
qed

abbreviation absorb :: "(['process, 'residual] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)" where
  "absorb \<I> \<equiv> absorb_downward \<I> \<squnion> absorb_upward \<I>"

lemma smashing_determinization: "absorb \<I> OO silent\<inverse>\<inverse> = absorb_downward \<I> OO silent\<inverse>\<inverse>"
proof -
  have "absorb \<I> OO silent\<inverse>\<inverse> = absorb_downward \<I> OO silent\<inverse>\<inverse> \<squnion> absorb_upward \<I> OO silent\<inverse>\<inverse>"
    by simp
  also have "\<dots> = absorb_downward \<I> OO silent\<inverse>\<inverse> \<squnion> absorb_downward \<I> OO silent\<inverse>\<inverse>"
    by (simp add: deterministic_smashing_equality)
  also have "\<dots> = absorb_downward \<I> OO silent\<inverse>\<inverse>"
    by simp
  finally show ?thesis .
qed

lemma derived_lift_equals_lift: "absorb (\<X> OO silent) = lift \<X>"
proof -
  have "absorb_downward (\<X> OO silent) \<le> lift \<X>"
  proof -
    have "silent\<inverse>\<inverse> OO (\<X> OO silent) = silent\<inverse>\<inverse> OO (silent OO lift \<X>)"
      by (simp add: std_silent_naturality)
    also have "\<dots> = (silent\<inverse>\<inverse> OO silent) OO lift \<X>"
      by (simp add: relcompp_assoc)
    also have "\<dots> \<le> (=) OO lift \<X>"
      by (simp add: silent_right_uniqueness relcompp_mono)
    also have "\<dots> = lift \<X>"
      by (fact eq_OO)
    finally show ?thesis .
  qed
  moreover have "absorb_upward (\<X> OO silent) = lift \<X>"
  proof -
    have "lift ((\<X> OO silent) OO silent\<inverse>\<inverse>) = lift (\<X> OO (silent OO silent\<inverse>\<inverse>))"
      by (simp add: relcompp_assoc)
    also have "\<dots> = lift (\<X> OO (=))"
      by (simp add: silent_left_uniqueness_and_left_totality)
    also have "\<dots> = lift \<X>"
      by (simp add: OO_eq)
    finally show ?thesis .
  qed
  ultimately show "absorb_downward (\<X> OO silent) \<squnion> absorb_upward (\<X> OO silent) = lift \<X>"
    by (simp add: sup.absorb_iff2)
qed

sublocale weak_residual silent absorb
proof
  fix \<I> :: "['process, 'residual] \<Rightarrow> bool" and \<J>
  assume "\<I> \<le> \<J>"
  then show "absorb_downward \<I> \<squnion> absorb_upward \<I> \<le> absorb_downward \<J> \<squnion> absorb_upward \<J>"
    by (intro sup_mono) (fact absorb_downward_monotonicity, fact absorb_upward_monotonicity)
next
  fix \<I> :: "['process, 'residual] \<Rightarrow> bool"
  have "silent OO absorb_downward \<I> = \<I>"
  proof -
    have "silent OO (silent\<inverse>\<inverse> OO \<I>) = (silent OO silent\<inverse>\<inverse>) OO \<I>"
      by (simp add: relcompp_assoc)
    also have "\<dots> = (=) OO \<I>"
      by (simp add: silent_left_uniqueness_and_left_totality)
    also have "\<dots> = \<I>"
      by (fact eq_OO)
    finally show ?thesis .
  qed
  moreover have "silent OO absorb_upward \<I> \<le> \<I>"
  proof -
    have "silent OO lift (\<I> OO silent\<inverse>\<inverse>) = (\<I> OO silent\<inverse>\<inverse>) OO silent"
      by (simp add: std_silent_naturality)
    also have "\<dots> = \<I> OO (silent\<inverse>\<inverse> OO silent)"
      by (fact relcompp_assoc)
    also have "\<dots> \<le> \<I> OO (=)"
      by (simp add: silent_right_uniqueness relcompp_mono)
    also have "\<dots> = \<I>"
      by (fact OO_eq)
    finally show ?thesis .
  qed
  ultimately show "silent OO (absorb_downward \<I> \<squnion> absorb_upward \<I>) = \<I>"
    by (simp add: sup.absorb_iff1)
next
  have "absorb_downward silent \<le> (=)"
    by (fact silent_right_uniqueness)
  moreover have "absorb_upward silent = (=)"
  proof -
    have "lift (silent OO silent\<inverse>\<inverse>) = lift (=)"
      by (simp add: silent_left_uniqueness_and_left_totality)
    also have "\<dots> = (=)"
      by (fact lift_equality_preservation)
    finally show ?thesis .
  qed
  ultimately show "absorb_downward silent \<squnion> absorb_upward silent = (=)"
    by (simp add: sup.absorb_iff2)
next
  fix \<I> :: "['process, 'residual] \<Rightarrow> bool" and \<J> :: "['process, 'residual] \<Rightarrow> bool"
  let ?keep_bottom = "absorb_downward \<I> OO absorb_downward \<J>"
  let ?keep_bottom_alt = "absorb_upward \<I> OO absorb_downward \<J>"
  let ?keep_middle = "absorb_downward \<I> OO absorb_upward \<J>"
  let ?keep_top = "absorb_upward \<I> OO absorb_upward \<J>"
  have keep_bottom_equality: "?keep_bottom = ?keep_bottom_alt"
  proof -
    have "absorb_downward \<I> OO (silent\<inverse>\<inverse> OO \<J>) = (absorb_downward \<I> OO silent\<inverse>\<inverse>) OO \<J>"
      by (simp add: relcompp_assoc)
    also have "\<dots> = (absorb_upward \<I> OO silent\<inverse>\<inverse>) OO \<J>"
      by (simp add: deterministic_smashing_equality)
    also have "\<dots> = absorb_upward \<I> OO (silent\<inverse>\<inverse> OO \<J>)"
      by (fact relcompp_assoc)
    finally show ?thesis .
  qed
  let ?lhs = "(absorb_downward \<I> \<squnion> absorb_upward \<I>) OO (absorb_downward \<J> \<squnion> absorb_upward \<J>)"
  let ?rhs = "absorb_downward (\<I> OO absorb \<J>) \<squnion> absorb_upward (\<I> OO absorb \<J>)"
  have "?lhs = ?keep_bottom \<squnion> ?keep_middle \<squnion> ?keep_top"
  proof -
    have "?lhs = (?keep_bottom \<squnion> ?keep_bottom_alt) \<squnion> (?keep_middle \<squnion> ?keep_top)"
      by simp
    also have "\<dots> = (?keep_bottom \<squnion> ?keep_bottom) \<squnion> (?keep_middle \<squnion> ?keep_top)"
      by (simp add: keep_bottom_equality)
    also have "\<dots> = ?keep_bottom \<squnion> (?keep_middle \<squnion> ?keep_top)"
      by simp
    also have "\<dots> = ?keep_bottom \<squnion> ?keep_middle \<squnion> ?keep_top"
      by (simp add: sup_assoc)
    finally show ?thesis .
  qed
  moreover have "?rhs = ?keep_bottom \<squnion> ?keep_middle \<squnion> ?keep_top"
  proof -
    have "absorb_downward (\<I> OO absorb \<J>) = ?keep_bottom \<squnion> ?keep_middle"
    proof -
      have "silent\<inverse>\<inverse> OO (\<I> OO absorb \<J>) = (silent\<inverse>\<inverse> OO \<I>) OO absorb \<J>"
        by (simp add: relcompp_assoc)
      also have "\<dots> = ?keep_bottom \<squnion> ?keep_middle"
        by (fact relcompp_distrib)
      finally show ?thesis .
    qed
    moreover have "absorb_upward (\<I> OO absorb \<J>) = ?keep_top"
    proof-
      have "lift ((\<I> OO absorb \<J>) OO silent\<inverse>\<inverse>) = lift (\<I> OO (absorb \<J> OO silent\<inverse>\<inverse>))"
        by (simp add: relcompp_assoc)
      also have "\<dots> = lift (\<I> OO (absorb_downward \<J> OO silent\<inverse>\<inverse>))"
        using smashing_determinization
        by simp
      also have "\<dots> = lift ((\<I> OO silent\<inverse>\<inverse>) OO (\<J> OO silent\<inverse>\<inverse>))"
        by (simp add: relcompp_assoc)
      also have "\<dots> = lift (\<I> OO silent\<inverse>\<inverse>) OO lift (\<J> OO silent\<inverse>\<inverse>)"
        by (fact lift_composition_preservation)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by simp
  qed
  ultimately show "?lhs = ?rhs"
    by simp
next
  fix \<X>
  show "absorb (\<X>\<inverse>\<inverse> OO silent) = (absorb (\<X> OO silent))\<inverse>\<inverse>"
    by (simp add: derived_lift_equals_lift lift_conversion_preservation)
qed

end

end
