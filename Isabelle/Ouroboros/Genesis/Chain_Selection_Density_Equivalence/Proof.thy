text \<open>
  FIXME:

    \<^item> Add documentation.
\<close>

theory Proof
imports
  Complex_Main
  Chains
  Protocol_Parameters
begin

fun fork_from_genesis :: "chain \<Rightarrow> chain \<Rightarrow> bool" where
  "fork_from_genesis [] \<C>' = True"
| "fork_from_genesis \<C> [] = True"
| "fork_from_genesis (B # \<C>) (B' # \<C>') = (B \<noteq> B')"

definition max_intersection_slot :: "chain \<Rightarrow> chain \<Rightarrow> slot" where
  [simp]: "max_intersection_slot \<C> \<C>' = (
    if fork_from_genesis \<C> \<C>'
    then
      genesis_slot
    else
      bslot (tip (longest_common_prefix \<C> \<C>')))"

definition denser_chain :: "nat \<Rightarrow> chain \<Rightarrow> chain \<Rightarrow> chain" where
  [simp]: "denser_chain s \<C> \<C>' = (
    let
      j = max_intersection_slot \<C> \<C>'
    in
      if |\<C>[0 ; j + s]| > |\<C>'[0 ; j + s]| then \<C> else \<C>')" \<comment> \<open>bias towards \<open>\<C>'\<close>\<close>

definition forks_at_most :: "nat \<Rightarrow> chain \<Rightarrow> chain \<Rightarrow> bool" where
  [iff]: "forks_at_most k \<C> \<C>' \<longleftrightarrow> (
    if
      fork_from_genesis \<C> \<C>'
    then
      |\<C>| \<le> k
    else
      |drop ( |longest_common_prefix \<C> \<C>'| ) \<C>| \<le> k)"

definition longer_chain :: "chain \<Rightarrow> chain \<Rightarrow> chain" where
  [simp]: "longer_chain \<C> \<C>' = (if |\<C>| > |\<C>'| then \<C> else \<C>')" \<comment> \<open>bias towards \<open>\<C>'\<close>\<close>

definition better_chain :: "nat \<Rightarrow> nat \<Rightarrow> chain \<Rightarrow> chain \<Rightarrow> chain" where
  [simp]: "better_chain k s \<C> \<C>' = (
    if forks_at_most k \<C> \<C>' then
      longer_chain \<C> \<C>'
    else
      denser_chain s \<C> \<C>')"

lemma disjoint_tails_max_intersection_slot:
  assumes "longest_common_prefix \<C> \<C>' \<noteq> []"
  shows "max_intersection_slot (B # \<C>) (B # \<C>') = max_intersection_slot \<C> \<C>'"
proof -
  have "max_intersection_slot (B # \<C>) (B # \<C>') = bslot (tip (B # longest_common_prefix \<C> \<C>'))"
    by simp
  also from assms have "\<dots> = max_intersection_slot \<C> \<C>'"
    unfolding max_intersection_slot_def using fork_from_genesis.simps(3)
    by (metis longest_common_prefix.elims last.simps)
  finally show ?thesis .
qed

lemma common_prefix_is_subchain:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
  shows "longest_common_prefix \<C> \<C>' = \<C>[genesis_slot ; sl]"
  using assms
proof (induction \<C> \<C>' rule: longest_common_prefix.induct[case_names non_empty fst_empty snd_empty])
  case (non_empty B \<C> B' \<C>')
  then show ?case
  proof (cases "B = B'")
    case True
    then show ?thesis
    proof (cases "longest_common_prefix \<C> \<C>' \<noteq> []")
      case True
      from non_empty.prems(1,2) have "is_valid_chain \<C>" and "is_valid_chain \<C>'"
        using chain_tail_validity by (blast, blast)
      moreover from non_empty.prems(3) and \<open>B = B'\<close> and True have "sl = max_intersection_slot \<C> \<C>'"
        using disjoint_tails_max_intersection_slot by simp
      ultimately have *: "longest_common_prefix \<C> \<C>' = \<C>[genesis_slot ; sl]"
        using non_empty.IH and \<open>B = B'\<close> by simp
      then have "B # longest_common_prefix \<C> \<C>' = B # \<C>[genesis_slot ; sl]"
        by blast
      with \<open>B = B'\<close> have "longest_common_prefix (B # \<C>) (B' # \<C>') = B # \<C>[genesis_slot ; sl]"
        by simp
      also have "\<dots> = (B # \<C>)[genesis_slot ; sl]"
      proof -
        from True and * have "filter (\<lambda>B. bslot B \<in> {genesis_slot..sl}) \<C> \<noteq> []"
          by simp
        then have "\<exists>B' \<in> set \<C>. bslot B' \<in> {genesis_slot..sl}"
          by (fastforce intro: filter_False)
        moreover from non_empty.prems(1) have "bslot B < bslot B'" if "B' \<in> set \<C>" for B'
          using that by force
        ultimately show ?thesis
          by fastforce
      qed
      finally show ?thesis .
    next
      case False
      with \<open>B = B'\<close> have *: "longest_common_prefix (B # \<C>) (B' # \<C>') = [B]"
        by simp
      moreover from \<open>B = B'\<close> and * and non_empty.prems(3) have "sl = bslot B"
        by simp
      with non_empty.prems(1) have "\<C>[genesis_slot ; sl] = []"
        using chain_tail_prefix_emptiness by blast
      ultimately show ?thesis
        using \<open>sl = bslot B\<close> by simp
    qed
  next
    case False
    then have "longest_common_prefix (B # \<C>) (B' # \<C>') = []"
      by simp
    with False and non_empty.prems(1,3) show ?thesis
      unfolding max_intersection_slot_def
      using genesis_slot_not_in_chain and fork_from_genesis.simps(3) by presburger
  qed
next
  case (fst_empty \<C>')
  then show ?case
    by simp
next
  case (snd_empty \<C>)
  then show ?case
    using genesis_slot_not_in_chain by (auto dest: fork_from_genesis.elims(3))
qed

(* Lemma 21.1 *)
lemma denser_chain_is_longer_chain:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "bslot (tip \<C>) \<le> sl + s"
    and "bslot (tip \<C>') \<le> sl + s"
  shows "denser_chain s \<C> \<C>' = longer_chain \<C> \<C>'"
proof -
  from assms(1,2,4,5) have "\<C>[genesis_slot ; sl + s] = \<C>" and "\<C>'[genesis_slot ; sl + s] = \<C>'"
    using right_maximal_subchain_identity by (blast, blast)
  with assms(3) show ?thesis
    by simp
qed

context protocol_parameters
begin

text \<open>
  NOTES:

  \<^item> The ``CG from CP'' property guarantees that in an interval of \<open>s\<close> slots an honest chain must
    grow by at least \<open>k\<close> blocks with overwhelming probability with \<open>s\<close> being at least \<open>3k/f\<close>. See
    -CITE HERE-.

  \<^item> The statement ``at the onset of slot \<open>sl\<close>'' is approximated by @{term \<open>bslot (tip \<C>) \<le> sl\<close>}.
\<close>
theorem chain_growth_from_common_prefix:
  assumes "s \<ge> default_window_size"
    and "\<C> \<noteq> []"
    and "bslot (tip \<C>) \<le> sl"
    and "sl\<^sub>1 + s \<le> sl\<^sub>2"
    and "sl\<^sub>2 \<le> sl"
  shows "|\<C>[sl\<^sub>1 ; sl\<^sub>2]| \<ge> k"
  sorry

lemma chain_tip_slot_boundedness:
  assumes "is_valid_chain \<C>"
    and "\<C> \<noteq> []"
    and "\<C>[Suc sl ;] = []"
  shows "bslot (tip \<C>) \<le> sl"
  using assms
proof (induction \<C>)
  case Nil
  then show ?case
    by simp
next
  case (Cons B \<C>)
  from Cons.prems(3) have "filter (\<lambda>B. bslot B \<ge> Suc sl) (B # \<C>) = []"
    by auto
  then have "\<not> bslot B' \<ge> Suc sl" if "B' \<in> set (B # \<C>)" for B'
    using that by (metis filter_empty_conv)
  then have "\<C>[Suc sl ;] = []"
    by simp
  then show ?case
  proof -
    { assume "\<C> \<noteq> []"
      with Cons.IH and Cons.prems(1) and \<open>\<C>[Suc sl ;] = []\<close> have "bslot (last \<C>) \<le> sl"
        using chain_tail_validity by blast
      with \<open>\<C> \<noteq> []\<close> have ?thesis
        by simp }
    with Cons.prems(3) show ?thesis
      by fastforce
  qed
qed

lemma chain_tip_within_window:
  assumes "is_valid_chain \<C>"
    and "\<C> \<noteq> []"
    and "|\<C>[sl ;]| \<le> k"
    and "s \<ge> default_window_size"
  shows "bslot (tip \<C>) \<le> sl + s"
proof (rule ccontr)
  assume *: "\<not> bslot (tip \<C>) \<le> sl + s"
  show False
  proof (cases "\<C>[Suc sl + s ;] \<noteq> []")
    case True
    from assms(1,4) have "\<C>[sl ; sl + s] @ \<C>[Suc (sl + s) ;] = \<C>[sl ;]"
      using chain_partition_by_interval by simp
    with assms(3) have "|\<C>[sl ; sl + s] @ \<C>[Suc (sl + s) ;]| \<le> k"
      by metis
    with True have "|\<C>[sl ; sl + s]| < k"
      by (fastforce dest: le_Suc_ex)
    moreover from assms(2,4) have "\<not> |\<C>[sl ; sl + s]| < k"
      using chain_growth_from_common_prefix by (meson leD nat_le_linear)
    ultimately show ?thesis
      by contradiction
  next
    case False
    with assms(1,2) have "bslot (tip \<C>) \<le> sl + s"
      using chain_tip_slot_boundedness by simp
    with * show ?thesis
      by contradiction
  qed
qed

lemma chain_within_maximum_rollback:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "|\<C>[sl ;]| \<le> k"
  shows "forks_at_most k \<C> \<C>'"
proof (cases "fork_from_genesis \<C> \<C>'")
  case True
  with assms(3) have "sl = genesis_slot"
    by simp
  with assms(1) have "\<C> = \<C>[Suc sl ;]"
    using left_maximal_subchain_identity by simp
  with True and assms(4) and \<open>sl = genesis_slot\<close> show ?thesis
    by simp
next
  case False
  with assms(1-3) have "longest_common_prefix \<C> \<C>' = \<C>[genesis_slot ; sl]"
    using common_prefix_is_subchain by blast
  with assms(1) have "drop ( |longest_common_prefix \<C> \<C>'| ) \<C> = \<C>[Suc sl ;]"
    using chain_partition_by_slot by (simp add: append_eq_conv_conj)
  moreover from assms(1,4) have "|\<C>[Suc sl ;]| \<le> k"
    using adjacent_slots_subchain_suffix and dual_order.trans by (fastforce dest: suffix_length_le)
  ultimately show ?thesis
    using False by simp
qed

(* lemma 21.2 *)
lemma chain_selection_density_equivalence:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "|\<C>[sl ;]| \<le> k"
    and "|\<C>'[sl ;]| \<le> k"
    and "s \<ge> default_window_size"
  shows "denser_chain s \<C> \<C>' = better_chain k s \<C> \<C>'"
proof -
  from assms(1-4) have "forks_at_most k \<C> \<C>'"
    by (fact chain_within_maximum_rollback)
  then have *: "better_chain k s \<C> \<C>' = longer_chain \<C> \<C>'"
    unfolding better_chain_def by presburger
  consider
      "\<C> = []" and "\<C>' = []"
    | "\<C> = []" and "\<C>' \<noteq> []"
    | (snd_empty) "\<C> \<noteq> []" and "\<C>' = []"
    | (non_empty) "\<C> \<noteq> []" and "\<C>' \<noteq> []"
    by blast
  then show ?thesis
  proof cases
    case snd_empty
    have "denser_chain s \<C> \<C>' = \<C>"
    proof -
      from assms(3) and \<open>\<C>' = []\<close> have "sl = genesis_slot"
        by (auto dest: fork_from_genesis.elims(3))
      with \<open>\<C> \<noteq> []\<close> and assms(1,4,6) have "bslot (tip \<C>) \<le> s"
        using chain_tip_within_window by fastforce
      with assms(1) have "\<C>[genesis_slot ; s] = \<C>"
        by (rule right_maximal_subchain_identity)
      with assms(3) and \<open>\<C>' = []\<close> and \<open>sl = genesis_slot\<close> show ?thesis
        unfolding denser_chain_def by simp
    qed
    also from \<open>\<C>' = []\<close> have "\<dots> = longer_chain \<C> \<C>'"
      unfolding longer_chain_def by simp
    finally show ?thesis
      using * ..
  next
    case non_empty
    with assms(1-6) have "bslot (tip \<C>) \<le> sl + s" and "bslot (tip \<C>') \<le> sl + s"
      using chain_tip_within_window by (blast, blast)
    with assms(1-3) and * show ?thesis
      using denser_chain_is_longer_chain by simp
  qed simp_all
qed

end

end
