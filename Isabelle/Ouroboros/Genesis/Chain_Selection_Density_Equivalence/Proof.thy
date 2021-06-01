section \<open> Equivalence proof \<close>

theory Proof
imports
  Complex_Main
  Chains
  Protocol_Parameters
begin

text \<open>
  TODO:

  \<^item> The current version of the equivalence proof assumes that the contesting chains have been
  created by @{emph \<open>honest\<close>} parties. According to Edsko and others, lifting this restriction
  would result in a major formalization effort.

  \<^item> Related to the previous point: There is a hole in the equivalence proof related to the
  impossibility of a specific scenario, namely the counter-example in which two chains \<open>\<C>\<close> and \<open>\<C>'\<close>
  have the same density but the candidate chain \<open>\<C>'\<close> is longer than the local chain \<open>\<C>\<close>. In this
  scenario, it holds that \<open>denser_chain s \<C> \<C>' = \<C>\<close> but \<open>longer_chain \<C> \<C>' = \<C>'\<close>. Assuming chain
  honesty, this scenario cannot happen, so we need to add an extra assumption that rules it out.
\<close>

text \<open>
  We define a function to check whether two chains fork from the genesis block, i.e., that their
  intersection is the genesis block:
\<close>

fun fork_from_genesis :: "chain \<Rightarrow> chain \<Rightarrow> bool" where
  "fork_from_genesis [] \<C>' = True"
| "fork_from_genesis \<C> [] = True"
| "fork_from_genesis (B # \<C>) (B' # \<C>') = (B \<noteq> B')"

text \<open>
  Given two chains, we can calculate the maximum slot in which both chains intersect:
\<close>

definition max_intersection_slot :: "chain \<Rightarrow> chain \<Rightarrow> slot" where
  [simp]: "max_intersection_slot \<C> \<C>' = (
    if fork_from_genesis \<C> \<C>'
    then
      genesis_slot
    else
      bslot (tip (longest_common_prefix \<C> \<C>')))"

text \<open>
  According to Definition 21.2 in @{cite "cardano-consensus-tr"}, we define what it means for a
  chain to be denser than another chain in a given window:
\<close>

definition denser_chain :: "nat \<Rightarrow> chain \<Rightarrow> chain \<Rightarrow> chain" where
  [simp]: "denser_chain s \<C> \<C>' = (
    let
      j = max_intersection_slot \<C> \<C>'
    in
      if |\<C>'[genesis_slot ; j + s]| > |\<C>[genesis_slot ; j + s]| then \<C>' else \<C>)" \<comment> \<open>bias towards \<open>\<C>\<close>\<close>

text \<open>
  We can check whether a chain \<open>\<C>'\<close> forks from a chain \<open>\<C>\<close> by at most \<open>k\<close> blocks:
\<close>

definition forks_at_most :: "nat \<Rightarrow> chain \<Rightarrow> chain \<Rightarrow> bool" where
  [iff]: "forks_at_most k \<C> \<C>' \<longleftrightarrow> |drop ( |longest_common_prefix \<C> \<C>'| ) \<C>| \<le> k"

text \<open>
  We define what it means for a chain to be longer than another chain:
\<close>

definition longer_chain :: "chain \<Rightarrow> chain \<Rightarrow> chain" where
  [simp]: "longer_chain \<C> \<C>' = (if |\<C>'| > |\<C>| then \<C>' else \<C>)" \<comment> \<open>bias towards \<open>\<C>\<close>\<close>

text \<open>
  According to Figure 10 of @{cite "genesis-paper"}, we define what it means for a chain to be
  better than another chain within a given window and a given maximum rollback:
\<close>

definition better_chain :: "nat \<Rightarrow> nat \<Rightarrow> chain \<Rightarrow> chain \<Rightarrow> chain" where
  [simp]: "better_chain k s \<C> \<C>' = (
    if forks_at_most k \<C> \<C>' then
      longer_chain \<C> \<C>'
    else
      denser_chain s \<C> \<C>')"

text \<open>
  If the longest common prefix of two chains is not empty, and both chains start with the same
  block, then the intersection of the two chains is the intersection of both tails:
\<close>

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

text \<open>
  The longest common prefix of two chains is the prefix of either chain up to, and including, the
  intersection of the two chains:
\<close>

lemma longest_common_prefix_alt_def:
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

text \<open>
  The following lemma establishes the commutativity of @{const \<open>fork_from_genesis\<close>}:
\<close>

lemma fork_from_genesis_commutativity:
  shows "fork_from_genesis \<C> \<C>' = fork_from_genesis \<C>' \<C>"
proof (cases "(\<C>, \<C>')" rule: fork_from_genesis.cases)
  case (1 \<C>')
  have "fork_from_genesis [] \<C>'"
    by simp
  moreover have "fork_from_genesis \<C>' []"
    by (blast intro: fork_from_genesis.elims(3))
  ultimately show ?thesis
    using 1 by simp
qed auto

text \<open>
  The following lemma establishes the commutativity of @{const \<open>max_intersection_slot\<close>}:
\<close>

lemma max_intersection_slot_commutativity:
  shows "max_intersection_slot \<C> \<C>' = max_intersection_slot \<C>' \<C>"
proof (cases "fork_from_genesis \<C> \<C>'")
  case True
  then show ?thesis
    using fork_from_genesis_commutativity by simp
next
  case False
  have "longest_common_prefix \<C> \<C>' = longest_common_prefix \<C>' \<C>"
    by (simp add:
          longest_common_prefix_max_prefix
          longest_common_prefix_prefix1
          longest_common_prefix_prefix2
          prefix_order.eq_iff)
  then show ?thesis
    using fork_from_genesis_commutativity by simp
qed

text \<open>
  The subchains of two chains starting at the beginning and ending in the intersection point are
  equal:
\<close>

corollary intersecting_subchains_equality:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
  shows "\<C>[genesis_slot ; sl] = \<C>'[genesis_slot ; sl]"
proof -
  from assms have "longest_common_prefix \<C> \<C>' = \<C>[genesis_slot ; sl]"
    using longest_common_prefix_alt_def by blast
  moreover have "max_intersection_slot \<C> \<C>' = max_intersection_slot \<C>' \<C>"
    by (rule max_intersection_slot_commutativity)
  with assms have "longest_common_prefix \<C>' \<C> = \<C>'[genesis_slot ; sl]"
    using longest_common_prefix_alt_def by blast
  moreover have "longest_common_prefix \<C> \<C>' = longest_common_prefix \<C>' \<C>"
    by (simp add:
          longest_common_prefix_max_prefix
          longest_common_prefix_prefix1
          longest_common_prefix_prefix2
          prefix_order.eq_iff)
  ultimately show ?thesis
    by simp
qed

text \<open>
  The following is the formalization of Lemma 21.1 in Section 21.2.1 of
  @{cite "cardano-consensus-tr"}: When comparing two chains with an intersection that is at most \<open>s\<close>
  slots away from the two tips, the Density Rule just prefers the longer chain:
\<close>

lemma denser_chain_is_longer_chain_within_window:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "bslot (tip \<C>) \<le> sl + s"
    and "bslot (tip \<C>') \<le> sl + s"
  shows "denser_chain s \<C> \<C>' = longer_chain \<C> \<C>'"
proof -
  from assms(1,2,4,5) have "\<C>[genesis_slot ; sl + s] = \<C>" and "\<C>'[genesis_slot ; sl + s] = \<C>'"
    using maximal_closed_subchain_equality by (blast, blast)
  with assms(3) show ?thesis
    by simp
qed


text \<open>
  If the window \<open>s\<close> is a positive number, then an alternative formulation of the Density Rule can
  be given, in which only the densities of the intervals \<open>[sl + 1 ; sl + s]\<close> in both chains are
  taken into account, where \<open>sl\<close> is the intersection point:
\<close>

lemma positive_window_denser_chain_alt_def:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "s > 0"
  shows "denser_chain s \<C> \<C>' = (if |\<C>'[sl + 1 ; sl + s]| > |\<C>[sl + 1 ; sl + s]| then \<C>' else \<C>)"
proof -
  from assms(4) have "sl < sl + s"
    by auto
  with assms(1,2)
  have "\<C>[genesis_slot ; sl] @ \<C>[sl + 1 ; sl + s] = \<C>[genesis_slot ; sl + s]"
    and "\<C>'[genesis_slot ; sl] @ \<C>'[sl + 1 ; sl + s] = \<C>'[genesis_slot ; sl + s]"
    using closed_subchain_partitioning by (blast, blast)
  moreover from assms(1-3) have "\<C>[genesis_slot ; sl] = \<C>'[genesis_slot ; sl]"
    by (rule intersecting_subchains_equality)
  ultimately have "|\<C>[genesis_slot ; sl + s]| = |\<C>[genesis_slot ; sl]| + |\<C>[sl + 1 ; sl + s]|"
    and "|\<C>'[genesis_slot ; sl + s]| = |\<C>[genesis_slot ; sl]| + |\<C>'[sl + 1 ; sl + s]|"
    by (metis length_append)+
  with assms(3) show ?thesis
    unfolding denser_chain_def by simp
qed

text \<open>
  Also, an alternative formulation of the Longest Chain Rule can be given, in which only the lengths
  of the intervals \<open>[sl + 1 ; ]\<close> in both chains are taken into account, where \<open>sl\<close> is the
  intersection point:
\<close>

lemma longer_chain_alt_def:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
  shows "longer_chain \<C> \<C>' = (if |\<C>'[sl + 1 ;]| > |\<C>[sl + 1 ;]| then \<C>' else \<C>)"
proof -
  from assms(1,2)
    have "\<C>[genesis_slot ; sl] @ \<C>[sl + 1 ;] = \<C>"
      and "\<C>'[genesis_slot ; sl] @ \<C>'[sl + 1 ;] = \<C>'"
    using chain_partitioning by (blast, blast)
  moreover from assms(1-3) have "\<C>[genesis_slot ; sl] = \<C>'[genesis_slot ; sl]"
    by (rule intersecting_subchains_equality)
  ultimately have "|\<C>| = |\<C>[genesis_slot ; sl]| + |\<C>[sl + 1 ;]|"
    and "|\<C>'| = |\<C>[genesis_slot ; sl]| + |\<C>'[sl + 1 ;]|"
    by (metis length_append)+
  then show ?thesis
    unfolding longer_chain_def by simp
qed

context protocol_parameters
begin

text \<open>
  The ``CG from CP'' argument states that in an interval of \<open>s\<close> slots an honest chain must grow by
  at least \<open>k\<close> blocks with overwhelming probability, with \<open>s\<close> being at least \<open>3k/f\<close>, see Section 4
  of @{cite "genesis-praos-parametrization"}. One remark is in order: The version of the argument
  used in this work is not probabilistic but assumes that it @{emph \<open>always\<close>} holds, i.e., with
  probability equal to 1:
\<close>

abbreviation chain_growth_from_common_prefix :: bool where
  "chain_growth_from_common_prefix \<equiv>
    \<forall>k s \<C> sl\<^sub>1 sl\<^sub>2.
      s = default_window_size \<and>
      is_valid_chain \<C> \<and>
      \<C> \<noteq> [] \<and>
      sl\<^sub>1 + s = sl\<^sub>2 + 1 \<and>
      sl\<^sub>2 \<le> bslot (tip \<C>) \<longrightarrow> |\<C>[sl\<^sub>1 ; sl\<^sub>2]| \<ge> k"

text \<open>
  If there are at most \<open>k > 0\<close> blocks in the suffix of \<open>\<C>\<close> which starts at slot \<open>sl\<close>, then the first
  block in this suffix is at most \<open>s\<close> slots away from the tip of \<open>\<C>\<close>:
\<close>

lemma chain_tip_within_window:
  assumes "is_valid_chain \<C>"
    and "\<C> \<noteq> []"
    and "sl \<le> bslot (tip \<C>)"
    and "|\<C>[sl ;]| \<le> k"
    and "s = default_window_size"
    and "k > 0"
    and chain_growth_from_common_prefix
  shows "bslot (tip \<C>) + 1 \<le> sl + s"
proof (rule ccontr)
  assume *: "\<not> bslot (tip \<C>) + 1 \<le> sl + s"
  show False
  proof (cases "\<C>[Suc (sl + s - 1) ;] \<noteq> []")
    case True
    from assms(5,6) have "s > 0"
      using default_window_greater_or_equal_than_k by (blast dest: less_le_trans)
    then have "sl \<le> sl + s - 1"
      by linarith
    with assms(1) have "\<C>[sl ; sl + s - 1] @ \<C>[(sl + s - 1) + 1 ;] = \<C>[sl ;]"
      using right_open_subchain_partitioning by simp
    with assms(4) have "|\<C>[sl ; sl + s - 1] @ \<C>[(sl + s - 1) + 1 ;]| \<le> k"
      by simp
    with True have "|\<C>[sl ; sl + s - 1]| < k"
      by (fastforce dest: le_Suc_ex)
    moreover from \<open>s > 0\<close> and assms(1,2,5,7) and * have "\<not> |\<C>[sl ; sl + s - 1]| < k"
      by (simp add: leD)
    ultimately show ?thesis
      by contradiction
  next
    case False
    have "bslot (tip \<C>) + 1 \<le> sl + s"
    proof -
      from assms(1,2) and False have f2: "bslot (tip \<C>) \<le> sl + s - 1"
        using chain_tip_slot_boundedness by simp
      with assms(5,6) show ?thesis
        using default_window_greater_or_equal_than_k by simp
    qed 
    with * show ?thesis
      by contradiction
  qed
qed

text \<open>
  When comparing two chains with an intersection that is at most \<open>k\<close> blocks away from the two tips,
  where \<open>k\<close> is a positive value, the Density Rule and the Longest Chain Rule are equivalent:
\<close>

lemma with_rollback_density_length_equivalence:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "|\<C>[sl + 1 ;]| \<le> k"
    and "|\<C>'[sl + 1 ;]| \<le> k"
    and "s = default_window_size"
    and "k > 0"
    and chain_growth_from_common_prefix
  shows "denser_chain s \<C> \<C>' = longer_chain \<C> \<C>'"
proof -
  \<comment> \<open>We must consider the following 3 cases:\<close>
  consider
      (snd_empty) "\<C>' = []"
    | (only_fst_empty) "\<C> = []" and "\<C>' \<noteq> []"
    | (non_empty) "\<C> \<noteq> []" and "\<C>' \<noteq> []"
    by blast
  then show ?thesis
  proof cases
    \<comment> \<open>In case  \<open>\<C>'\<close> is empty:\<close>
    case snd_empty
    have "denser_chain s \<C> \<C>' = \<C>"
    proof -
      from assms(3) and \<open>\<C>' = []\<close> have "sl = genesis_slot"
        by (auto dest: fork_from_genesis.elims(3))
      then have "\<not> ( |[]| > |\<C>[genesis_slot ; sl + s]| )"
        by simp
      with \<open>\<C>' = []\<close> show ?thesis
        by simp
    qed
    moreover have "\<not> ( |[]| > |\<C>| )"
      by simp
    with \<open>\<C>' = []\<close> show ?thesis
      by simp
  next
    \<comment> \<open>In case only \<open>\<C>\<close> is empty:\<close>
    case only_fst_empty
    \<comment> \<open>\<open>\<C>'\<close> is denser than \<open>\<C>\<close>:\<close>
    have "denser_chain s \<C> \<C>' = \<C>'"
    proof -
      \<comment> \<open>Since for this case \<open>\<C>\<close> is empty, then obviously the intersection is the genesis slot:\<close>
      from assms(3) and \<open>\<C> = []\<close> have "sl = genesis_slot"
        by (auto dest: fork_from_genesis.elims(3))
      \<comment> \<open>Then, since by assumption the intersection is at most \<open>k\<close> blocks away from the tip of \<open>\<C>'\<close>,
         then the intersection is at most \<open>s\<close> slots away from the tip of \<open>\<C>'\<close> by aux lemma:\<close>
      with assms(2,5,6,8) and only_fst_empty(2) have "bslot (tip \<C>') \<le> s"
        using chain_tip_within_window and genesis_succesor_subchain_equality by fastforce
      \<comment> \<open>Then, by aux lemma, the subchain of \<open>\<C>'\<close> in the interval from the genesis slot to \<open>s\<close> is
         \<open>\<C>'\<close> itself:\<close>
      with assms(2) have "\<C>'[genesis_slot ; s] = \<C>'"
        by (rule maximal_closed_subchain_equality)
      \<comment> \<open>Therefore, by definition of \<open>denser_chain\<close>, the thesis holds:\<close>
      with assms(3) and \<open>\<C> = []\<close> and \<open>sl = genesis_slot\<close> show ?thesis
        unfolding denser_chain_def by simp
    qed
    \<comment> \<open>Furthermore, by definition of \<open>longer_chain\<close>, \<open>\<C>'\<close> is also longer than \<open>\<C>\<close>:\<close>
    also from \<open>\<C> = []\<close> have "\<dots> = longer_chain \<C> \<C>'"
      unfolding longer_chain_def by simp
    \<comment> \<open>Finally, since we proved that better is longer, the thesis holds:\<close>
    finally show ?thesis .
  next
    \<comment> \<open>In case both chains are non-empty:\<close>
    case non_empty
    \<comment> \<open>The intersection is at most \<open>s\<close> slots away from the tips:\<close>
    from assms(1,2) and non_empty
    have "\<C>[sl + 1 ;] = \<C>[sl + 1 ; bslot (tip \<C>)]" and "\<C>'[sl + 1 ;] = \<C>'[sl + 1 ; bslot (tip \<C>')]"
      using right_open_subchain_tip_boundedness by (blast, blast)
    with assms(4,5) have "|\<C>[sl + 1 ; bslot (tip \<C>)]| \<le> k" and "|\<C>'[sl + 1 ; bslot (tip \<C>')]| \<le> k"
      by auto
    with assms(1,2,4-8) and non_empty
    have "bslot (tip \<C>) + 1 \<le> (sl + 1) + s" and "bslot (tip \<C>') + 1 \<le> (sl + 1) + s"
      using chain_tip_within_window by (smt Suc_eq_plus1 not_less_eq_eq trans_le_add1)+
    \<comment> \<open>Then by lemma 21.1 the thesis holds\<close>
    with assms(1-3) show ?thesis
      using denser_chain_is_longer_chain_within_window by simp
  qed
qed

text \<open>
  Also, for the case in which \<open>k = 0\<close>, i.e., when comparing two chains with an intersection that is
  at most \<open>0\<close> blocks away from the two tips, this means that both chains are equal and consequently
  the Density Rule and the Longest Chain Rule are equivalent:
\<close>

lemma no_rollback_density_length_equivalence:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "|\<C>[sl + 1 ;]| = 0"
    and "|\<C>'[sl + 1 ;]| = 0"
  shows "denser_chain s \<C> \<C>' = longer_chain \<C> \<C>'"
proof -
  from assms(1,2,4,5) have "\<C> = \<C>[genesis_slot ; sl]" and "\<C>' = \<C>'[genesis_slot ; sl]"
    using chain_partitioning by (metis append_Nil2 length_0_conv)+
  with assms(1,2,3) have "\<C> = \<C>'"
    using intersecting_subchains_equality by metis
  then show ?thesis
    by simp
qed

text \<open>
  Finally, when comparing two chains with an intersection that is at most \<open>k\<close> blocks away from the
  two tips, the Density Rule and the Longest Chain Rule are equivalent:
\<close>

lemma density_length_equivalence:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "|\<C>[sl + 1 ;]| \<le> k"
    and "|\<C>'[sl + 1;]| \<le> k"
    and "s = default_window_size"
    and chain_growth_from_common_prefix
  shows "denser_chain s \<C> \<C>' = longer_chain \<C> \<C>'"
proof (cases "k = 0")
  case True
  from True and assms(4,5) have "|\<C>[sl + 1 ;]| = 0" and "|\<C>'[sl + 1 ;]| = 0"
    by (blast, blast)
  with assms(1-3) show ?thesis
    using no_rollback_density_length_equivalence by blast
next
  case False
  with assms(1-7) show ?thesis
    using with_rollback_density_length_equivalence by blast
qed

text \<open>
  Now, given two chains \<open>\<C>\<close> and \<open>\<C>'\<close> with an intersection that is at most \<open>k\<close> blocks away from the
  tip of \<open>\<C>\<close>, then it holds that \<open>\<C>'\<close> forks from \<open>\<C>\<close> by at most \<open>k\<close> blocks:
\<close>

lemma chain_within_maximum_rollback:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "|\<C>[sl + 1 ;]| \<le> k"
  shows "forks_at_most k \<C> \<C>'"
proof -
  from assms(1-3) have "longest_common_prefix \<C> \<C>' = \<C>[genesis_slot ; sl]"
    using longest_common_prefix_alt_def by blast
  with assms(1) have "drop ( |longest_common_prefix \<C> \<C>'| ) \<C> = \<C>[sl + 1 ;]"
    using chain_partitioning by (simp add: append_eq_conv_conj)
  moreover from assms(1,4) have "|\<C>[sl + 1 ;]| \<le> k"
    using adjacent_slots_subchain_suffix and dual_order.trans by (fastforce dest: suffix_length_le)
  ultimately show ?thesis
    by simp
qed

text \<open>
  Also, given two chains \<open>\<C>\<close> and \<open>\<C>'\<close> with an intersection that is more than \<open>k\<close> blocks away from
  the tip of \<open>\<C>\<close>, then it holds that \<open>\<C>'\<close> does not fork from \<open>\<C>\<close> by at most \<open>k\<close> blocks:
\<close>

lemma chain_outside_maximum_rollback:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "sl = max_intersection_slot \<C> \<C>'"
    and "|\<C>[sl + 1 ;]| > k"
  shows "\<not> forks_at_most k \<C> \<C>'"
proof (unfold forks_at_most_def, simp only: not_le)
  from assms(1-3) have "longest_common_prefix \<C> \<C>' = \<C>[genesis_slot ; sl]"
    by (rule longest_common_prefix_alt_def)
  moreover from assms(1) have "\<C>[genesis_slot ; sl] @ \<C>[sl + 1 ;] = \<C>"
    by (rule chain_partitioning)
  then have "\<C>[sl + 1 ;] = drop |\<C>[genesis_slot ; sl]| \<C>"
    by (simp add: append_eq_conv_conj)
  ultimately show "|drop |longest_common_prefix \<C> \<C>'| \<C>| > k"
    using assms(4) by simp
qed

text \<open>
  For the case in which \<open>k = 0\<close> (and consequently \<open>s = 0\<close>), when comparing two chains \<open>\<C>\<close> and \<open>\<C>'\<close>
  such that \<open>\<C>\<close> is a prefix of \<open>\<C>'\<close>, the Density Rule and the Longest Chain Rule are equivalent:
\<close>

lemma prefix_density_length_equivalence:
  assumes "is_valid_chain \<C>'"
    and "\<C> \<preceq> \<C>'"
    and "s = default_window_size"
    and "k = 0"
  shows "denser_chain s \<C> \<C>' = longer_chain \<C> \<C>'"
proof -
  let ?sl = "max_intersection_slot \<C> \<C>'"
  show ?thesis
  proof (cases "\<C> = \<C>'")
    case True
    from True have "\<not> ( |\<C>'[genesis_slot ; ?sl + s]| > |\<C>[genesis_slot ; ?sl + s]| )"
      by blast
    then have "denser_chain s \<C> \<C>' = \<C>"
      by simp
    moreover from True have "|\<C>| = |\<C>'|"
      by simp
    then have "longer_chain \<C> \<C>' = \<C>"
      by simp
    ultimately show ?thesis ..
  next
    case False
    \<comment> \<open> Counter-example (i.e., same density but candidate is longer) \<close>
    then show ?thesis
      sorry
  qed
qed

text \<open>
  Now, for the case in which \<open>k = 0\<close> (and consequently \<open>s = 0\<close>), the Density Rule and the Genesis
  Rule are equivalent:
\<close>

lemma no_rollback_density_betterness_equivalence:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "s = default_window_size"
    and "k = 0"
  shows "denser_chain s \<C> \<C>' = better_chain k s \<C> \<C>'"
proof (cases "forks_at_most k \<C> \<C>'")
  case True
  with assms(4) have "drop ( |longest_common_prefix \<C> \<C>'| ) \<C> = []"
    by blast
  then have "longest_common_prefix \<C> \<C>' = \<C>"
    by (meson drop_eq_Nil longest_common_prefix_prefix1 prefix_length_prefix prefix_order.eq_iff)
  then have "\<C> \<preceq> \<C>'"
    using longest_common_prefix_prefix2[of \<C> \<C>'] by simp
  with assms(2-4) show ?thesis
    using prefix_density_length_equivalence by simp
next
  case False
  then show ?thesis
    by simp
qed

text \<open>
  Also, for the case in which \<open>k > 0\<close> (and consequently \<open>s > 0\<close>), the Density Rule and the Genesis
  Rule are equivalent:
\<close>

lemma with_rollback_density_betterness_equivalence:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "s = default_window_size"
    and "k > 0"
    and chain_growth_from_common_prefix
  shows "denser_chain s \<C> \<C>' = better_chain k s \<C> \<C>'"
proof -
  let ?sl = "max_intersection_slot \<C> \<C>'"
  from assms(3,4) have "s > 0"
    using default_window_greater_or_equal_than_k by (blast dest: less_le_trans)
  then have "?sl < ?sl + s"
    by auto
  consider
    (a) "|\<C>[?sl + 1 ;]| \<le> k" and "|\<C>'[?sl + 1 ;]| \<le> k"
  | (b) "|\<C>[?sl + 1 ;]| \<le> k" and "|\<C>'[?sl + 1;]| > k"
  | (c) "|\<C>[?sl + 1 ;]| > k"
    using not_less by blast
  then show ?thesis
  proof cases
    case a
    with assms show ?thesis
      using density_length_equivalence unfolding better_chain_def by simp
  next
    case b
    with assms(1,2) have "forks_at_most k \<C> \<C>'"
      using chain_within_maximum_rollback by presburger
    from assms(1,2) and b have "longer_chain \<C> \<C>' = \<C>'"
      using longer_chain_alt_def by simp
    consider
        (1) "\<C> = []" and "\<C>' = []"
      | (2) "\<C> = []" and "\<C>' \<noteq> []"
      | (3) "\<C> \<noteq> []" and "\<C>' = []"
      | (4) "\<C> \<noteq> []" and "\<C>' \<noteq> []"
      by blast
    then show ?thesis
    proof cases
      case 1
      with b show ?thesis
        using not_le by blast
    next
      case 2
      from \<open>\<C> = []\<close> have "?sl = genesis_slot"
        by simp
      from assms(2) have "\<C>'[genesis_slot + 1 ;] = \<C>'"
        by (rule genesis_succesor_subchain_equality)
      have "|\<C>'[genesis_slot ; s]| > 0"
      proof (cases "bslot (tip \<C>') < s")
        case True
        with assms(2) and \<open>\<C>' \<noteq> []\<close> show ?thesis
          using maximal_closed_subchain_equality by auto
      next
        case False
        have "genesis_slot + 1 + s = s + 1"
          by simp
        moreover from False have "s \<le> bslot (tip \<C>')"
          using not_less by blast
        ultimately have "|\<C>'[genesis_slot + 1 ; s]| \<ge> k"
          using \<open>\<C>' \<noteq> []\<close> and assms(2,3,5) by blast
        moreover have "\<C>'[genesis_slot ; s] = \<C>'[genesis_slot + 1 ; s]"
        proof -
          from assms(2) have "\<C>'[genesis_slot ; s] @ \<C>'[s + 1 ;] = \<C>'"
            by (rule chain_partitioning)
          moreover from assms(2) and \<open>s > 0\<close> and \<open>\<C>'[genesis_slot + 1 ;] = \<C>'\<close>
          have "\<C>'[genesis_slot + 1 ; s] @ \<C>'[s + 1 ;] = \<C>'"
            using right_open_subchain_partitioning by auto
          ultimately show ?thesis
            by (metis append_same_eq)
        qed
        ultimately show ?thesis
          using assms(4) by auto
      qed
      with \<open>\<C> = []\<close> have "denser_chain s \<C> \<C>' = \<C>'"
        by simp
      with \<open>longer_chain \<C> \<C>' = \<C>'\<close> show ?thesis
        by simp
    next
      case 3
      with b(2) show ?thesis
        by auto
    next
      case 4
      have "bslot (tip \<C>) \<le> ?sl + s"
      proof -
        from assms(1,3,4,5) and \<open>\<C> \<noteq> []\<close> and \<open>|\<C>[?sl + 1 ;] | \<le> k\<close> and \<open>s > 0\<close>
        have "bslot (tip \<C>) + 1 \<le> (?sl + 1) + s"
          using chain_tip_within_window
          by (metis One_nat_def Suc_leI add_mono_thms_linordered_semiring(1) nat_le_linear)
        then show ?thesis
          by linarith
      qed
      show ?thesis
      proof (cases "bslot (tip \<C>') \<le> ?sl + s")
        case True
        with assms(1,2) and \<open>bslot (tip \<C>) \<le> ?sl + s\<close> show ?thesis
          using denser_chain_is_longer_chain_within_window by auto
      next
        case False
        with assms(2,3,5) and \<open>\<C>' \<noteq> []\<close> have "|\<C>'[?sl + 1 ; ?sl + s]| \<ge> k"
          by (metis Suc_eq_plus1 nat_le_linear plus_nat.simps(2))
        then show ?thesis
        proof (cases "|\<C>[?sl + 1 ; ?sl + s]| = k \<and> |\<C>'[?sl + 1 ; ?sl + s]| = k")
          case True
          \<comment> \<open> Counter-example (i.e., same density but candidate is longer) \<close>
          then show ?thesis
            sorry
        next
          case False
          from False show ?thesis
            apply (simp only: de_Morgan_conj)
          proof (elim disjE)
            assume "|\<C>[?sl + 1 ; ?sl + s]| \<noteq> k"
            with assms(1) and \<open>|\<C>[?sl + 1 ;] | \<le> k\<close> and \<open>?sl < ?sl + s\<close>
            have "|\<C>[?sl + 1 ; ?sl + s]| < k"
              using right_open_subchain_partitioning
              by (metis (no_types, lifting) add_leE discrete length_append nat_less_le)
            moreover from \<open>|\<C>[?sl + 1 ; ?sl + s]| < k\<close> and \<open>|\<C>'[?sl + 1 ; ?sl + s]| \<ge> k\<close>
            have "|\<C>'[?sl + 1 ; ?sl + s]| > |\<C>[?sl + 1 ; ?sl + s]|"
              using less_le_trans by blast
            ultimately have "denser_chain s \<C> \<C>' = \<C>'"
              using \<open>s > 0\<close> and assms(1,2) and positive_window_denser_chain_alt_def by auto
            with \<open>longer_chain \<C> \<C>' = \<C>'\<close> show ?thesis
              by simp
          next
            assume "|\<C>'[?sl + 1 ; ?sl + s]| \<noteq> k"
            with \<open>k \<le> |\<C>'[?sl + 1 ; ?sl + s]|\<close> have "|\<C>'[?sl + 1 ; ?sl + s]| > k"
              by linarith
            with assms(1) and \<open>|\<C>[?sl + 1 ;] | \<le> k\<close> and \<open>?sl < ?sl + s\<close>
            have "|\<C>[?sl + 1 ; ?sl + s]| \<le> k"
              using right_open_subchain_partitioning by (metis add_leE discrete length_append)
            moreover from \<open>|\<C>'[?sl + 1 ; ?sl + s]| > k\<close> and \<open>|\<C>[?sl + 1 ; ?sl + s]| \<le> k\<close>
            have "|\<C>'[?sl + 1 ; ?sl + s]| > |\<C>[?sl + 1 ; ?sl + s]|"
              using le_less_trans by blast
            ultimately have "denser_chain s \<C> \<C>' = \<C>'"
              using \<open>s > 0\<close> and assms(1,2) and positive_window_denser_chain_alt_def by auto
            with \<open>longer_chain \<C> \<C>' = \<C>'\<close> show ?thesis
              by simp
          qed
        qed
      qed
    qed
  next
    case c
    with assms(1,2,3) show ?thesis
      using chain_outside_maximum_rollback by auto
  qed
qed

text \<open>
  Finally, we prove the main theorem: The Density Rule and the Genesis Rule are equivalent:
\<close>

theorem density_betterness_equivalence:
  assumes "is_valid_chain \<C>"
    and "is_valid_chain \<C>'"
    and "s = default_window_size"
    and chain_growth_from_common_prefix
  shows "denser_chain s \<C> \<C>' = better_chain k s \<C> \<C>'"
  using assms
    and no_rollback_density_betterness_equivalence
    and with_rollback_density_betterness_equivalence
  by (smt neq0_conv)

text \<open>
  Now, according to Figure 10 of @{cite "genesis-paper"}, we define $\textsf{maxvalid-bg}$:
\<close>

definition maxvalid_bg :: "chain \<Rightarrow> chain list \<Rightarrow> nat \<Rightarrow> chain" where
  [simp]: "maxvalid_bg \<C>\<^sub>l\<^sub>o\<^sub>c \<N> s = foldl (better_chain k s) \<C>\<^sub>l\<^sub>o\<^sub>c \<N>"

text \<open>
  Similarly, we define $\textsf{maxvalid-dr}$ based on the Density Rule:
\<close>

definition maxvalid_dr :: "chain \<Rightarrow> chain list \<Rightarrow> nat \<Rightarrow> chain" where
  [simp]: "maxvalid_dr \<C>\<^sub>l\<^sub>o\<^sub>c \<N> s = foldl (denser_chain s) \<C>\<^sub>l\<^sub>o\<^sub>c \<N>"

text \<open>
  Finally, we prove the equivalence of $\textsf{maxvalid-bg}$ and $\textsf{maxvalid-dr}$:
\<close>

theorem maxvalid_bg_maxvalid_dr_equivalence:
  assumes "\<forall>\<C> \<in> set \<N> \<union> {\<C>\<^sub>l\<^sub>o\<^sub>c}. is_valid_chain \<C>"
    and "s = default_window_size"
    and chain_growth_from_common_prefix
  shows "maxvalid_bg \<C>\<^sub>l\<^sub>o\<^sub>c \<N> s = maxvalid_dr \<C>\<^sub>l\<^sub>o\<^sub>c \<N> s"
  using assms
proof (induction \<N> arbitrary: \<C>\<^sub>l\<^sub>o\<^sub>c)
  case Nil
  then show ?case
    by simp
next
  case Cons
  then show ?case
    using density_betterness_equivalence
    unfolding maxvalid_bg_def and maxvalid_dr_def and denser_chain_def
    by (smt Un_insert_left Un_insert_right foldl.simps(2) insert_iff list.set(2))
qed

end

text \<open>
  Testing:
\<close>

abbreviation (input) test_k :: nat where "test_k \<equiv> 2"
abbreviation (input) test_f :: real where "test_f \<equiv> 1/2" \<comment> \<open>unused\<close>

definition "test_maxvalid_bg = protocol_parameters.maxvalid_bg test_k"
definition "test_maxvalid_dr = protocol_parameters.maxvalid_dr"

interpretation test_protocol_parameters: protocol_parameters test_k test_f
  rewrites "protocol_parameters.maxvalid_bg test_k = test_maxvalid_bg"
  unfolding test_maxvalid_bg_def
  by unfold_locales simp_all

abbreviation make_test_block :: "slot \<Rightarrow> block" ("B\<^bsub>_\<^esub>") where
  "B\<^bsub>sl\<^esub> \<equiv> (sl, ())"

abbreviation make_test_chain :: "slot list \<Rightarrow> chain" ("\<langle>_\<rangle>") where
  "\<langle>ss\<rangle> \<equiv> map make_test_block ss"

abbreviation test_equivalence where
  "test_equivalence \<C>\<^sub>l\<^sub>o\<^sub>c \<N> s \<equiv> test_maxvalid_bg \<C>\<^sub>l\<^sub>o\<^sub>c \<N> s = test_maxvalid_dr \<C>\<^sub>l\<^sub>o\<^sub>c \<N> s"

value "test_equivalence \<langle>[1, 2]\<rangle> [] 10"
value "test_equivalence \<langle>[1, 2]\<rangle> [\<langle>[1, 2, 3]\<rangle>] 10"
value "test_equivalence \<langle>[1, 2, 3]\<rangle> [\<langle>[1, 2]\<rangle>] 10"
value "test_equivalence \<langle>[1, 2]\<rangle> [\<langle>[4, 5]\<rangle>] 10"
value "test_equivalence \<langle>[1, 3, 7, 8, 9, 10]\<rangle> [\<langle>[1, 2, 4]\<rangle>] 5"
value "test_equivalence \<langle>[1, 2, 7, 8, 9, 10]\<rangle> [\<langle>[1, 2, 3, 8, 9, 10]\<rangle>] 5"

end
