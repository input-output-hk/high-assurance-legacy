theory Chains
imports
  "HOL-Library.Sublist"
  Blocks
begin

type_synonym chain = "block list"

abbreviation (input) tip :: "chain \<Rightarrow> block" where
  "tip \<equiv> last"

abbreviation is_slot_increasing :: "chain \<Rightarrow> bool" where
  "is_slot_increasing \<C> \<equiv> sorted_wrt (\<lambda>B B'. bslot B < bslot B') \<C>"

abbreviation starts_after_genesis :: "chain \<Rightarrow> bool" where
  "starts_after_genesis \<C> \<equiv> \<C> \<noteq> [] \<longrightarrow> bslot (hd \<C>) > genesis_slot"

abbreviation is_valid_chain :: "chain \<Rightarrow> bool" where
  "is_valid_chain \<C> \<equiv> is_slot_increasing \<C> \<and> starts_after_genesis \<C>"

lemma chain_tail_validity:
  assumes "is_valid_chain (B # \<C>)"
  shows "is_valid_chain \<C>"
  using assms by (induction \<C>) auto

notation length (\<open>|_|\<close>)

lemma valid_chain_is_sorted_wrt_slot:
  assumes "is_valid_chain \<C>"
    and "0 \<le> i"
    and "i \<le> j"
    and "j < |\<C>|"
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

datatype slot_interval = ClosedInterval slot slot | RightOpenInterval slot

fun subchain_including :: "chain \<Rightarrow> slot_interval \<Rightarrow> chain" where
  "subchain_including \<C> (ClosedInterval sl sl') = filter (\<lambda>B. bslot B \<in> {sl..sl'}) \<C>"
| "subchain_including \<C> (RightOpenInterval sl) = filter (\<lambda>B. bslot B \<ge> sl) \<C>"

syntax
  "_SUBCHAIN_INCLUDING_CLOSED_INTERVAL" :: "chain \<Rightarrow> slot \<Rightarrow> slot \<Rightarrow> chain" ("_[_;_]" [70, 0] 70)
  "_SUBCHAIN_INCLUDING_RIGHT_OPEN_INTERVAL" :: "chain \<Rightarrow> slot \<Rightarrow> slot \<Rightarrow> chain" ("_[_;] " [70, 0] 70)

translations
  "\<C>[sl\<^sub>i;sl\<^sub>j]" \<rightleftharpoons> "CONST subchain_including \<C> (CONST ClosedInterval sl\<^sub>i sl\<^sub>j)"
  "\<C>[sl;]" \<rightleftharpoons> "CONST subchain_including \<C> (CONST RightOpenInterval sl)"

lemma left_maximal_subchain_identity:
  assumes "is_valid_chain \<C>"
  shows "\<C>[Suc genesis_slot ;] = \<C>"
proof -
  have "bslot B \<ge> Suc genesis_slot" if "B \<in> set \<C>" for B
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

lemma right_maximal_subchain_identity:
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

lemma chain_partition_by_interval:
  assumes "is_valid_chain \<C>"
    and "sl\<^sub>1 \<le> sl\<^sub>2"
  shows "\<C>[sl\<^sub>1 ; sl\<^sub>2] @ \<C>[Suc sl\<^sub>2 ;] = \<C>[sl\<^sub>1 ;]"
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
    also from Cons.IH and \<open>is_valid_chain \<C>\<close> and assms(2) have "\<dots> = B # \<C>[sl\<^sub>1 ; sl\<^sub>2] @ \<C>[Suc sl\<^sub>2 ;]"
      by auto
    also have "\<dots> = (B # \<C>)[sl\<^sub>1 ; sl\<^sub>2] @ (B # \<C>)[Suc sl\<^sub>2 ;]"
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

lemma chain_partition_by_slot:
  assumes "is_valid_chain \<C>"
  shows "(\<C>[genesis_slot ; sl]) @ (\<C>[Suc sl ;]) = \<C>"
  using assms and chain_partition_by_interval by fastforce

lemma adjacent_slots_subchain_suffix:
  assumes "is_valid_chain \<C>"
  shows "suffix (\<C>[Suc sl ;]) (\<C>[sl ;])"
  by (intro suffixI, subst chain_partition_by_interval[OF assms order_refl], simp)

lemma genesis_slot_not_in_chain:
  assumes "is_valid_chain \<C>"
  shows "\<C>[genesis_slot ; genesis_slot] = []"
proof -
  from assms have "\<C>[Suc genesis_slot ;] = \<C>"
    by (rule left_maximal_subchain_identity)
  with assms have "\<C>[genesis_slot ; genesis_slot] @ \<C> = \<C>"
    using chain_partition_by_slot by metis
  then show ?thesis
    by blast
qed

lemma chain_tail_prefix_emptiness:
  assumes "is_valid_chain (B # \<C>)"
  shows "\<C>[genesis_slot ; bslot B] = []"
proof -
  from assms have "bslot B < bslot B'" if "B' \<in> set \<C>" for B'
    using that by simp
  then have "filter (\<lambda>B'. bslot B' \<in> {0..bslot B}) \<C> = []"
    by (fastforce intro: filter_False)
  then show ?thesis
    by simp
qed

end
