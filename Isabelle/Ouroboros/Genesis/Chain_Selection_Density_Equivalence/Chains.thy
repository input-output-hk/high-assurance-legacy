section \<open> Chains \<close>

theory Chains
imports
  "HOL-Library.Sublist"
  Blocks
begin

text \<open>
  As defined in Section 3.1 of @{cite "genesis-paper"}, a @{emph \<open>chain\<close>} is simply a sequence of
  blocks. We do not record the genesis block explicitly as part of the chain:
\<close>

type_synonym chain = "block list"

text \<open>
  For the purposes of this work, a chain is @{emph \<open>valid\<close>} if either:

  1. It is empty; or

  2. It starts after the genesis slot and has strictly increasing slots.
\<close>

abbreviation is_slot_increasing :: "chain \<Rightarrow> bool" where
  "is_slot_increasing \<C> \<equiv> sorted_wrt (\<lambda>B B'. bslot B < bslot B') \<C>"

abbreviation starts_after_genesis :: "chain \<Rightarrow> bool" where
  "starts_after_genesis \<C> \<equiv> \<C> \<noteq> [] \<longrightarrow> bslot (hd \<C>) > genesis_slot"

abbreviation is_valid_chain :: "chain \<Rightarrow> bool" where
  "is_valid_chain \<C> \<equiv> is_slot_increasing \<C> \<and> starts_after_genesis \<C>"

abbreviation (input) tip :: "chain \<Rightarrow> block" where
  "tip \<equiv> last"

text \<open>
  If a non-empty chain is valid then so is its tail:
\<close>

lemma chain_tail_validity:
  assumes "is_valid_chain (B # \<C>)"
  shows "is_valid_chain \<C>"
  using assms by (induction \<C>) auto

notation length (\<open>|_|\<close>)

text \<open>
  A valid chain is sorted w.r.t. the slot field:
\<close>

lemma valid_chain_is_sorted_wrt_slot:
  assumes "is_valid_chain \<C>"
    and "0 \<le> i" and "i \<le> j" and "j < |\<C>|"
  shows "bslot (\<C> ! i) \<le> bslot (\<C> ! j)"
proof (cases "i < j")
  case True
  with assms(1,4) have "bslot (\<C> ! i) < bslot (\<C> ! j)"
    by (fastforce simp add: sorted_wrt_iff_nth_less)
  then show ?thesis
    by (rule less_imp_le)
next
  case False
  with assms(3) show ?thesis
    by simp
qed

notation prefix (infix \<open>\<preceq>\<close> 50)

text \<open>
  A prefix of a valid chain is also a valid chain:
\<close>

lemma chain_prefix_validity:
  assumes "is_valid_chain \<C>'"
    and "\<C> \<preceq> \<C>'"
  shows "is_valid_chain \<C>"
proof -
  from assms have "is_slot_increasing \<C>"
    unfolding prefix_def using sorted_wrt_append by blast
  moreover from assms have "starts_after_genesis \<C>"
    unfolding prefix_def by auto
  ultimately show ?thesis
    by simp
qed

text \<open>
  According to Section 3.1 of @{cite "genesis-paper"}, we define the concept of subchain induced by
  a given interval of slots:
\<close>

datatype slot_interval = ClosedInterval slot slot | RightOpenInterval slot

fun induced_subchain :: "chain \<Rightarrow> slot_interval \<Rightarrow> chain" where
  "induced_subchain \<C> (ClosedInterval sl\<^sub>1 sl\<^sub>2) = filter (\<lambda>B. bslot B \<in> {sl\<^sub>1..sl\<^sub>2}) \<C>"
| "induced_subchain \<C> (RightOpenInterval sl) = filter (\<lambda>B. bslot B \<ge> sl) \<C>"

syntax
  "_INDUCED_SUBCHAIN_CLOSED_INTERVAL" :: "chain \<Rightarrow> slot \<Rightarrow> slot \<Rightarrow> chain" ("_[_;_]" [70, 0, 0] 70)
  "_INDUCED_SUBCHAIN_RIGHT_OPEN_INTERVAL" :: "chain \<Rightarrow> slot \<Rightarrow> slot \<Rightarrow> chain" ("_[_;] " [70, 0] 70)

translations
  "\<C>[sl\<^sub>1;sl\<^sub>2]" \<rightleftharpoons> "CONST induced_subchain \<C> (CONST ClosedInterval sl\<^sub>1 sl\<^sub>2)"
  "\<C>[sl;]" \<rightleftharpoons> "CONST induced_subchain \<C> (CONST RightOpenInterval sl)"

text \<open>
  A right-open subchain is implicitly bounded by the chain tip's slot:
\<close>

lemma right_open_subchain_tip_boundedness:
  assumes "is_valid_chain \<C>"
    and "\<C> \<noteq> []"
  shows "\<C>[sl ;] = \<C>[sl ; bslot (tip \<C>)]"
proof -
  have "bslot B \<ge> sl \<longleftrightarrow> bslot B \<in> {sl..bslot (tip \<C>)}" if "B \<in> set \<C>" for B
  proof
    assume "bslot B \<ge> sl"
    from that obtain i where "i < |\<C>|" and "B = \<C> ! i"
      by (auto simp add: in_set_conv_nth)
    with assms(1) and that have "bslot (\<C> ! i) \<le> bslot (\<C> ! ( |\<C>| - 1 ))"
      by (simp add: valid_chain_is_sorted_wrt_slot)
    also from assms(2) have "\<dots> = bslot (tip \<C>)"
      by (simp add: last_conv_nth)
    finally show "bslot B \<in> {sl..bslot (tip \<C>)}"
      using \<open>B = \<C> ! i\<close> and \<open>sl \<le> bslot B\<close> and atLeastAtMost_iff by blast
  next
    assume "bslot B \<in> {sl..bslot (tip \<C>)}"
    then show "bslot B \<ge> sl"
      by auto
  qed
  then have "filter (\<lambda>B. bslot B \<ge> sl) \<C> = filter (\<lambda>B. bslot B \<in> {sl..bslot (tip \<C>)}) \<C>"
    by (metis (no_types, lifting) filter_cong)
  then show ?thesis
    by auto
qed

text \<open>
  Given a chain, its subchain starting right after the genesis slot is the original chain:
\<close>

lemma genesis_succesor_subchain_equality:
  assumes "is_valid_chain \<C>"
  shows "\<C>[genesis_slot + 1 ;] = \<C>"
proof -
  have "bslot B \<ge> genesis_slot + 1" if "B \<in> set \<C>" for B
  proof -
    from that have "\<C> \<noteq> []"
      by fastforce
    from that obtain i where "i < |\<C>|" and "B = \<C> ! i"
      by (auto simp add: in_set_conv_nth)
    with assms and \<open>\<C> \<noteq> []\<close> have "bslot (hd \<C>) \<le> bslot (\<C> ! i)"
      using valid_chain_is_sorted_wrt_slot by (simp add: hd_conv_nth)
    with \<open>B = \<C> ! i\<close> and assms and \<open>\<C> \<noteq> []\<close> show ?thesis
      by simp
  qed
  then show ?thesis
    by (simp add: filter_id_conv)
qed

text \<open>
  Given a chain, its subchain starting at a given slot \<open>sl\<^sub>1\<close> can be partitioned into two subchains
  by a subsequent slot \<open>sl\<^sub>2\<close> as the partition point:
\<close>

lemma right_open_subchain_partitioning:
  assumes "is_valid_chain \<C>"
    and "sl\<^sub>1 \<le> sl\<^sub>2"
  shows "\<C>[sl\<^sub>1 ; sl\<^sub>2] @ \<C>[sl\<^sub>2 + 1 ;] = \<C>[sl\<^sub>1 ;]"
  using assms
proof (induction \<C>)
  case Nil
  then show ?case
    by simp
next
  case (Cons B \<C>)
  from Cons.prems(1) have "is_valid_chain \<C>"
    by (rule chain_tail_validity)
  then show ?case
  proof (cases "bslot B \<ge> sl\<^sub>1")
    case True
    then have "(B # \<C>)[sl\<^sub>1 ;] = B # \<C>[sl\<^sub>1 ;]"
      by simp
    also from Cons.IH and \<open>is_valid_chain \<C>\<close> and assms(2) have "\<dots> = B # \<C>[sl\<^sub>1 ; sl\<^sub>2] @ \<C>[sl\<^sub>2 + 1 ;]"
      by auto
    also have "\<dots> = (B # \<C>)[sl\<^sub>1 ; sl\<^sub>2] @ (B # \<C>)[sl\<^sub>2 + 1 ;]"
    proof (cases "bslot B \<le> sl\<^sub>2")
      case True
      with \<open>(B # \<C>)[sl\<^sub>1 ;] = B # \<C>[sl\<^sub>1 ;]\<close> show ?thesis
        using not_less_eq_eq by fastforce
    next
      case False
      with Cons.prems(1) have "bslot B \<notin> {sl\<^sub>1..sl\<^sub>2}" if "B \<in> set \<C>" for B
        using that by auto
      then have "\<C>[sl\<^sub>1 ; sl\<^sub>2] = []"
        by simp
      with False show ?thesis
        by (simp add: not_less_eq_eq)
    qed
    finally show ?thesis ..
  next
    case False
    with Cons.IH and \<open>is_valid_chain \<C>\<close> and assms(2) show ?thesis
      by auto
  qed
qed

text \<open>
  A closed subchain can be partitioned into two subchains by a intermediate slot as the partition
  point:
\<close>

lemma closed_subchain_partitioning:
  assumes "is_valid_chain \<C>"
    and "sl\<^sub>0 \<le> sl\<^sub>1" and "sl\<^sub>1 < sl\<^sub>2"
  shows "\<C>[sl\<^sub>0 ; sl\<^sub>1] @ \<C>[sl\<^sub>1 + 1 ; sl\<^sub>2] = \<C>[sl\<^sub>0 ; sl\<^sub>2]"
proof -
  from assms have "\<C>[sl\<^sub>0 ; sl\<^sub>2] @ \<C>[sl\<^sub>2 + 1 ;] = \<C>[sl\<^sub>0 ;]"
    using right_open_subchain_partitioning by auto
  moreover from assms(1,2) have "\<C>[sl\<^sub>0 ; sl\<^sub>1] @ \<C>[sl\<^sub>1 + 1 ;] = \<C>[sl\<^sub>0 ;]"
    by (rule right_open_subchain_partitioning)
  ultimately have "\<C>[sl\<^sub>0 ; sl\<^sub>2] @ \<C>[sl\<^sub>2 + 1 ;] = \<C>[sl\<^sub>0 ; sl\<^sub>1] @ \<C>[sl\<^sub>1 + 1 ;]"
    by simp
  moreover from assms(1,3) have "\<C>[sl\<^sub>1 + 1 ; sl\<^sub>2] @ \<C>[sl\<^sub>2 + 1 ;] = \<C>[sl\<^sub>1 + 1;]"
    using right_open_subchain_partitioning by simp
  ultimately have "\<C>[sl\<^sub>0 ; sl\<^sub>2] @ \<C>[sl\<^sub>2 + 1 ;] = (\<C>[sl\<^sub>0 ; sl\<^sub>1] @ \<C>[sl\<^sub>1 + 1 ; sl\<^sub>2]) @ \<C>[sl\<^sub>2 + 1 ;]"
    by simp
  then show ?thesis
    by simp (* NOTE: `append_eq_append_conv` does the trick here *)
qed


text \<open>
  Given a chain, its subchain starting at the genesis slot and ending at a slot greater or equal to
  the chain tip's slot is the original chain:
\<close>

lemma maximal_closed_subchain_equality:
  assumes "is_valid_chain \<C>"
    and "bslot (tip \<C>) \<le> sl"
  shows "\<C>[genesis_slot ; sl] = \<C>"
proof -
  have "bslot B \<le> sl" if "B \<in> set \<C>" for B
  proof -
    from that obtain i where "i < |\<C>|" and "B = \<C> ! i"
      by (auto simp add: in_set_conv_nth)
    with assms(1) and that have "bslot (\<C> ! i) \<le> bslot (\<C> ! ( |\<C>| - 1 ))"
      by (simp add: valid_chain_is_sorted_wrt_slot)
    moreover from that have "\<C> \<noteq> []"
      by fastforce
    ultimately show ?thesis
      using \<open>B = \<C> ! i\<close> and assms(2) by (fastforce simp add: last_conv_nth)
  qed
  then show ?thesis
    by (simp add: filter_id_conv)
qed

text \<open>
  A chain can be partitioned into two subchains by a slot \<open>sl\<close> as the partition point:
\<close>

lemma chain_partitioning:
  assumes "is_valid_chain \<C>"
  shows "\<C>[genesis_slot ; sl] @ \<C>[sl + 1 ;] = \<C>"
  using assms and right_open_subchain_partitioning by fastforce

text \<open>
  Given a chain, its subchain starting at slot \<open>sl + 1\<close> is a suffix of its subchain starting at slot
  \<open>sl\<close>:
\<close>

lemma adjacent_slots_subchain_suffix:
  assumes "is_valid_chain \<C>"
  shows "suffix (\<C>[sl + 1 ;]) (\<C>[sl ;])"
  by (intro suffixI, subst right_open_subchain_partitioning[OF assms order_refl], simp)

text \<open>
  The subchain starting and ending at the genesis slot is empty:
\<close>

lemma genesis_slot_not_in_chain:
  assumes "is_valid_chain \<C>"
  shows "\<C>[genesis_slot ; genesis_slot] = []"
proof -
  from assms have "\<C>[genesis_slot + 1 ;] = \<C>"
    by (rule genesis_succesor_subchain_equality)
  with assms have "\<C>[genesis_slot ; genesis_slot] @ \<C> = \<C>"
    using chain_partitioning by metis
  then show ?thesis
    by blast
qed

text \<open>
  Given a non-empty chain, its subchain starting at the genesis slot and ending at the slot of its
  head is empty:
\<close>

lemma chain_tail_prefix_emptiness:
  assumes "is_valid_chain (B # \<C>)"
  shows "\<C>[genesis_slot ; bslot B] = []"
proof -
  from assms have "bslot B < bslot B'" if "B' \<in> set \<C>" for B'
    using that by simp
  then have "filter (\<lambda>B'. bslot B' \<in> {genesis_slot..bslot B}) \<C> = []"
    by (fastforce intro: filter_False)
  then show ?thesis
    by simp
qed

text \<open>
  If there are no blocks in a chain with slots greater than \<open>sl\<close>, then the tip of the chain is
  slot-bounded by \<open>sl\<close>:
\<close>

lemma chain_tip_slot_boundedness:
  assumes "is_valid_chain \<C>"
    and "\<C> \<noteq> []"
    and "\<C>[sl + 1 ;] = []"
  shows "bslot (tip \<C>) \<le> sl"
  using assms
proof (induction \<C>)
  case Nil
  then show ?case
    by simp
next
  case (Cons B \<C>)
  from Cons.prems(3) have "filter (\<lambda>B. bslot B \<ge> sl + 1) (B # \<C>) = []"
    by auto
  then have "\<not> bslot B' \<ge> sl + 1" if "B' \<in> set (B # \<C>)" for B'
    using that by (metis filter_empty_conv)
  then have "\<C>[sl + 1 ;] = []"
    by simp
  then show ?case
  proof -
    { assume "\<C> \<noteq> []"
      with Cons.IH and Cons.prems(1) and \<open>\<C>[sl + 1 ;] = []\<close> have "bslot (tip \<C>) \<le> sl"
        using chain_tail_validity by blast
      with \<open>\<C> \<noteq> []\<close> have ?thesis
        by simp }
    with Cons.prems(3) show ?thesis
      by fastforce
  qed
qed

end
