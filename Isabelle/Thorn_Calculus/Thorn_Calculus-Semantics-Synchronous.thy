section \<open>Synchronous Semantics\<close>

theory "Thorn_Calculus-Semantics-Synchronous"
imports
  "Relation_Methods.Equivalence"
  "Transition_Systems-New.Transition_Systems-Weak_Mutation_Systems"
  "Thorn_Calculus-Actions"
  "Thorn_Calculus-Processes"
begin

definition dependent_on_chan_at :: "nat \<Rightarrow> val family \<Rightarrow> bool" where
  [simp]: "dependent_on_chan_at i X \<longleftrightarrow> (\<exists>a\<^sub>1 a\<^sub>2. \<Delta>\<^bsub>i\<^esub> X a\<^sub>1 \<noteq> \<Delta>\<^bsub>i\<^esub> X a\<^sub>2)"

lemma dependent_on_chan_at_after_on_suffix_adapted:
  assumes "i \<le> n"
  shows "dependent_on_chan_at i (X \<guillemotleft> on_suffix (Suc n) \<E>) \<longleftrightarrow> dependent_on_chan_at i X"
proof -
  have "
    \<Delta>\<^bsub>i\<^esub> (X \<guillemotleft> on_suffix (Suc n) \<E>) a\<^sub>1 \<noteq> \<Delta>\<^bsub>i\<^esub> (X \<guillemotleft> on_suffix (Suc n) \<E>) a\<^sub>2
    \<longleftrightarrow>
    \<Delta>\<^bsub>i\<^esub> X a\<^sub>1 \<noteq> \<Delta>\<^bsub>i\<^esub> X a\<^sub>2"
    (is "?v \<longleftrightarrow> ?w")
    for a\<^sub>1 and a\<^sub>2
  proof -
    have "?v \<longleftrightarrow> \<Delta>\<^bsub>i\<^esub> X a\<^sub>1 \<guillemotleft> on_suffix n \<E> \<noteq> \<Delta>\<^bsub>i\<^esub> X a\<^sub>2 \<guillemotleft> on_suffix n \<E>"
      using \<open>i \<le> n\<close>
      by (simp only: deep_curry_after_on_suffix_adapted)
    also have "\<dots> \<longleftrightarrow> ?w"
      by (simp only: adapted_injectivity)
    finally show ?thesis .
  qed
  then show ?thesis
    by simp
qed

lemma dependent_on_chan_at_after_source_anchored_move_adapted:
  shows "dependent_on_chan_at i (X \<guillemotleft> move i j) \<longleftrightarrow> dependent_on_chan_at j X"
proof -
  have "\<Delta>\<^bsub>i\<^esub> (X \<guillemotleft> move i j) = \<Delta>\<^bsub>j\<^esub> X"
  proof -
    have "\<Delta>\<^bsub>i\<^esub> (X \<guillemotleft> move i j) = \<Delta>\<^bsub>i\<^esub> (\<nabla>\<^bsub>i\<^esub> (\<Delta>\<^bsub>j\<^esub> X))"
      by transfer simp
    also have "\<dots> = \<Delta>\<^bsub>j\<^esub> X"
      by (simp only: deep_curry_after_deep_uncurry pointfree_idE)
    finally show ?thesis .
  qed
  then show ?thesis
    by simp
qed

lemma dependent_on_chan_at_after_move_within_prefix_adapted:
  assumes "i < n" and "j < n"
  shows "dependent_on_chan_at n (X \<guillemotleft> move i j) \<longleftrightarrow> dependent_on_chan_at n X"
proof -
  have "
    \<Delta>\<^bsub>n\<^esub> (X \<guillemotleft> move i j) a\<^sub>1 \<noteq> \<Delta>\<^bsub>n\<^esub> (X \<guillemotleft> move i j) a\<^sub>2 \<longleftrightarrow> \<Delta>\<^bsub>n\<^esub> X a\<^sub>1 \<noteq> \<Delta>\<^bsub>n\<^esub> X a\<^sub>2"
    (is "?v \<longleftrightarrow> ?w")
    for a\<^sub>1 and a\<^sub>2
  proof -
    have "?v \<longleftrightarrow> \<Delta>\<^bsub>n\<^esub> X a\<^sub>1 \<guillemotleft> move i j \<noteq> \<Delta>\<^bsub>n\<^esub> X a\<^sub>2 \<guillemotleft> move i j"
      using \<open>i < n\<close> and \<open>j < n\<close>
      by (simp only: deeper_curry_after_move_adapted)
    also have "\<dots> \<longleftrightarrow> ?w"
      by (simp only: adapted_injectivity)
    finally show ?thesis .
  qed
  then show ?thesis
    by simp
qed

lemma not_dependent_on_chan_at:
  assumes "\<not> dependent_on_chan_at i X'"
  obtains X where "X' = X \<guillemotleft> remove i"
proof
  have "X' = (\<lambda>e. X' (insert_at i (e !! i) (delete_at i e)))"
    by (simp only: insert_at_after_delete_at)
  also have "\<dots> = (\<lambda>e. X' (insert_at i undefined (delete_at i e)))"
    using \<open>\<not> dependent_on_chan_at i X'\<close>
    unfolding dependent_on_chan_at_def and deep_curry_def
    by metis
  also have "\<dots> = X' \<circ> insert_at i undefined \<guillemotleft> remove i" (is "_ = ?X'")
    by transfer (simp only: comp_def)
  finally show "X' = ?X'" .
qed

inductive
  synchronous_transition :: "action \<Rightarrow> process family relation"
  (\<open>'(\<rightarrow>\<^sub>s\<lparr>_\<rparr>')\<close>)
and
  synchronous_transition_std :: "process family \<Rightarrow> action \<Rightarrow> process family \<Rightarrow> bool"
  (\<open>(_ \<rightarrow>\<^sub>s\<lparr>_\<rparr>/ _)\<close> [51, 0, 51] 50)
where
  \<comment> \<open>Standard notation:\<close>
  "P \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> Q \<equiv> (\<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr>) P Q" |
  \<comment> \<open>Execution of actions:\<close>
  sending:
    "A \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>0\<^esup> X\<rparr> \<zero>" |
  scope_opening:
    "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>Suc n\<^esup> X\<rparr> Q"
    if
      "i \<le> n"
    and
      "dependent_on_chan_at i X"
    and
      "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move n i\<rparr> Q \<guillemotleft> move n i" |
  receiving:
    "A \<triangleright> x. \<P> x \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e)" |
  communication:
    "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (P' \<parallel> Q')"
    if "\<eta> \<noteq> \<mu>" and "P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'" and "Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> Q'" |
  \<comment> \<open>Working in subsystems:\<close>
  parallel_left_io:
    "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P' \<parallel> Q \<guillemotleft> suffix n"
    if "P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'" |
  parallel_left_communication:
    "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P' \<parallel> Q"
    if "P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'" |
  parallel_right_io:
    "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P \<guillemotleft> suffix n \<parallel> Q'"
    if "Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q'" |
  parallel_right_communication:
    "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P \<parallel> Q'"
    if "Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'" |
  new_channel_io:
    "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> \<nu> a. \<Q> a"
    if "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> \<Q>" |
  new_channel_communication:
    "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nu> a. \<Q> a"
    if "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<Q>"

lemmas [induct_simp] =
  family_uncurry_after_stop
  family_uncurry_after_send
  family_uncurry_after_receive
  family_uncurry_after_parallel
  family_uncurry_after_new_channel

lemmas [induct_simp] =
  constant_function_family_uncurry
  constant_family_chan_family_uncurry
  chan_family_distinctness

lemma adapted_io_transition:
  assumes "S \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> T"
  shows "S \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> \<E>) n (X \<guillemotleft> on_suffix n \<E>)\<rparr> T \<guillemotleft> on_suffix n \<E>"
using assms proof (induction "IO \<eta> A n X" S T arbitrary: A n X \<E>)
  case sending
  show ?case
    unfolding \<open>Sending = \<eta>\<close> [symmetric]
    by
      (simp only:
        adapted_after_send
        adapted_after_stop
        identity_as_partial_on_suffix [symmetric]
        id_def
        synchronous_transition.sending
      )
next
  case (scope_opening i n X \<P> A Q \<E>)
  from \<open>dependent_on_chan_at i X\<close> have "dependent_on_chan_at i (X \<guillemotleft> on_suffix (Suc n) \<E>)"
    unfolding dependent_on_chan_at_after_on_suffix_adapted [OF \<open>i \<le> n\<close>] .
  moreover
  from scope_opening(4) have "
    \<nabla> \<P> \<guillemotleft> on_tail \<E>
    \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<guillemotleft> on_tail \<E> \<triangleleft> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move n i \<guillemotleft> on_suffix n (on_tail \<E>)\<rparr>
    Q \<guillemotleft> move n i \<guillemotleft> on_suffix n (on_tail \<E>)"
    unfolding \<open>Sending = \<eta>\<close> [symmetric]
    by (simp only:)
  moreover
  have "\<nabla> \<P> \<guillemotleft> on_tail \<E> = \<nabla> (\<lambda>a. (\<P> a \<guillemotleft> \<E>))"
    unfolding on_tail_def
    by transfer (simp add: comp_def)
  moreover
  have "A \<guillemotleft> tail \<guillemotleft> on_tail \<E> = A \<guillemotleft> \<E> \<guillemotleft> tail"
    by (simp add: composition_adapted [symmetric] suffix_after_on_suffix)
  moreover
  have "move n i \<bullet> on_suffix n (on_tail \<E>) = on_suffix (Suc n) \<E> \<bullet> move n i"
  proof -
    have "move n i \<bullet> on_suffix n (on_tail \<E>) = move n i \<bullet> on_suffix (Suc n) \<E>"
      using composition_as_partial_on_suffix [THEN fun_cong]
      by simp
    also have "\<dots> = on_suffix (Suc n) \<E> \<bullet> move n i"
      using \<open>i \<le> n\<close>
      by (simp only: move_after_on_suffix)
    finally show ?thesis .
  qed
  then have
    "X \<guillemotleft> move n i \<guillemotleft> on_suffix n (on_tail \<E>) = X \<guillemotleft> on_suffix (Suc n) \<E> \<guillemotleft> move n i"
  and
    "Q \<guillemotleft> move n i \<guillemotleft> on_suffix n (on_tail \<E>) = Q \<guillemotleft> on_suffix (Suc n) \<E> \<guillemotleft> move n i"
    by (simp_all only: composition_adapted [symmetric])
  ultimately show ?case
    unfolding \<open>Sending = \<eta>\<close> [symmetric]
    using \<open>i \<le> n\<close>
    by (simp only: adapted_after_new_channel synchronous_transition.scope_opening)
next
  case (receiving A \<P> n X \<E>)
  have "
    A \<guillemotleft> \<E> \<triangleright> x. \<P> x \<guillemotleft> \<E>
    \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> \<E> \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> on_suffix n \<E>\<rparr>
    (\<lambda>e. (\<P> ((X \<guillemotleft> on_suffix n \<E>) e) \<guillemotleft> \<E> \<guillemotleft> suffix n) e)"
    (is "_ \<rightarrow>\<^sub>s\<lparr>_\<rparr> ?Q'")
    using synchronous_transition.receiving .
  moreover have "?Q' = (\<lambda>d. (\<P> (X d) \<guillemotleft> suffix n) d) \<guillemotleft> on_suffix n \<E>" (is "_ = ?R'")
  proof -
    have "?Q' = (\<lambda>e. (\<P> ((X \<guillemotleft> on_suffix n \<E>) e) \<guillemotleft> suffix n \<guillemotleft> on_suffix n \<E>) e)"
      by (simp only: composition_adapted [symmetric] suffix_after_on_suffix)
    also have "\<dots> = ?R'"
      by transfer (simp only: comp_def)
    finally show ?thesis .
  qed
  ultimately show ?case
    unfolding \<open>Receiving = \<eta>\<close> [symmetric]
    by (simp only: adapted_after_receive)
next
  case (parallel_left_io P A n X P' Q \<E>)
  from parallel_left_io(2) have "P \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> \<E>) n (X \<guillemotleft> on_suffix n \<E>)\<rparr> P' \<guillemotleft> on_suffix n \<E>" .
  then have "
    P \<guillemotleft> \<E> \<parallel> Q \<guillemotleft> \<E>
    \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> \<E>) n (X \<guillemotleft> on_suffix n \<E>)\<rparr>
    P' \<guillemotleft> on_suffix n \<E> \<parallel> Q \<guillemotleft> \<E> \<guillemotleft> suffix n"
    by (fact synchronous_transition.parallel_left_io)
  moreover have "P' \<guillemotleft> on_suffix n \<E> \<parallel> Q \<guillemotleft> \<E> \<guillemotleft> suffix n = (P' \<parallel> Q \<guillemotleft> suffix n) \<guillemotleft> on_suffix n \<E>"
    by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_on_suffix)
  ultimately show ?case
    by (simp only: adapted_after_parallel)
next
  case (parallel_right_io Q A n X Q' P \<E>)
  from parallel_right_io(2) have "Q \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> \<E>) n (X \<guillemotleft> on_suffix n \<E>)\<rparr> Q' \<guillemotleft> on_suffix n \<E>" .
  then have "
    P \<guillemotleft> \<E> \<parallel> Q \<guillemotleft> \<E>
    \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> \<E>) n (X \<guillemotleft> on_suffix n \<E>)\<rparr>
    P \<guillemotleft> \<E> \<guillemotleft> suffix n \<parallel> Q' \<guillemotleft> on_suffix n \<E>"
    by (fact synchronous_transition.parallel_right_io)
  moreover have "P \<guillemotleft> \<E> \<guillemotleft> suffix n \<parallel> Q' \<guillemotleft> on_suffix n \<E> = (P \<guillemotleft> suffix n \<parallel> Q') \<guillemotleft> on_suffix n \<E>"
    by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_on_suffix)
  ultimately show ?case
    by (simp only: adapted_after_parallel)
next
  case (new_channel_io \<P> A n X \<Q> \<E>)
  from new_channel_io(2) have "
    \<nabla> \<P> \<guillemotleft> on_tail \<E>
    \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail \<guillemotleft> on_tail \<E>) n (X \<guillemotleft> remove n \<guillemotleft> on_suffix n (on_tail \<E>))\<rparr>
    \<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> on_suffix n (on_tail \<E>)" .
  moreover
  have "\<nabla> \<P> \<guillemotleft> on_tail \<E> = \<nabla> (\<lambda>a. (\<P> a \<guillemotleft> \<E>))"
    unfolding on_tail_def
    by transfer (simp add: comp_def)
  moreover
  have "A \<guillemotleft> tail \<guillemotleft> on_tail \<E> = A \<guillemotleft> \<E> \<guillemotleft> tail"
    by (simp add: composition_adapted [symmetric] suffix_after_on_suffix)
  moreover
  have "X \<guillemotleft> remove n \<guillemotleft> on_suffix n (on_tail \<E>) = X \<guillemotleft> on_suffix n \<E> \<guillemotleft> remove n"
  proof -
    have "X \<guillemotleft> remove n \<guillemotleft> on_suffix n (on_tail \<E>) = X \<guillemotleft> remove n \<guillemotleft> on_suffix (Suc n) \<E>"
      using composition_as_partial_on_suffix [THEN fun_cong]
      by simp
    also have "\<dots> = X \<guillemotleft> on_suffix n \<E> \<guillemotleft> remove n"
      by (simp only: composition_adapted [symmetric] remove_after_on_suffix)
    finally show ?thesis .
  qed
  moreover
  have "\<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> on_suffix n (on_tail \<E>) = \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<Q> a \<guillemotleft> on_suffix n \<E>)"
  proof -
    have "\<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> on_suffix n (on_tail \<E>) = \<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> on_suffix (Suc n) \<E>"
      using composition_as_partial_on_suffix [THEN fun_cong]
      by simp
    also have "\<dots> = \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<Q> a \<guillemotleft> on_suffix n \<E>)"
      unfolding on_suffix_adapted_after_deep_uncurry [OF le_refl]
      by simp
    finally show ?thesis .
  qed
  ultimately show ?case
    by (simp only: adapted_after_new_channel synchronous_transition.new_channel_io)
qed

lemma adapted_communication_transition:
  assumes "S \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> T"
  shows "S \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> T \<guillemotleft> \<E>"
using assms proof (induction \<tau> S T arbitrary: \<E>)
  case (communication \<eta> \<mu> P A n X P' Q Q' \<E>)
  from \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close> have "P \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> \<E>) n (X \<guillemotleft> on_suffix n \<E>)\<rparr> P' \<guillemotleft> on_suffix n \<E>"
    by (fact adapted_io_transition)
  moreover
  from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> Q'\<close> have "Q \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>IO \<mu> (A \<guillemotleft> \<E>) n (X \<guillemotleft> on_suffix n \<E>)\<rparr> Q' \<guillemotleft> on_suffix n \<E>"
    by (fact adapted_io_transition)
  ultimately have "P \<guillemotleft> \<E> \<parallel> Q \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (P' \<guillemotleft> on_suffix n \<E> \<parallel> Q' \<guillemotleft> on_suffix n \<E>)"
    using \<open>\<eta> \<noteq> \<mu>\<close>
    by (intro synchronous_transition.communication)
  moreover have "\<star>\<^bsup>n\<^esup> (P' \<guillemotleft> on_suffix n \<E> \<parallel> Q' \<guillemotleft> on_suffix n \<E>) = \<star>\<^bsup>n\<^esup> (P' \<parallel> Q') \<guillemotleft> \<E>"
    by (simp only: adapted_after_create_channel_power adapted_after_parallel)
  ultimately show ?case
    by (simp only: adapted_after_parallel)
next
  case parallel_left_communication
  from parallel_left_communication(2) show ?case
    by (simp only: adapted_after_parallel synchronous_transition.parallel_left_communication)
next
  case parallel_right_communication
  from parallel_right_communication(2) show ?case
    by (simp only: adapted_after_parallel synchronous_transition.parallel_right_communication)
next
  case (new_channel_communication \<P> \<Q> \<E>)
  from new_channel_communication(2) have "\<nabla> \<P> \<guillemotleft> on_tail \<E> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<Q> \<guillemotleft> on_tail \<E>" .
  moreover
  have "\<nabla> \<P> \<guillemotleft> on_tail \<E> = \<nabla> (\<lambda>a. (\<P> a \<guillemotleft> \<E>))" and "\<nabla> \<Q> \<guillemotleft> on_tail \<E> = \<nabla> (\<lambda>a. \<Q> a \<guillemotleft> \<E>)"
    unfolding on_tail_def
    by (transfer, simp add: comp_def)+
  ultimately show ?case
    by (simp only: adapted_after_new_channel synchronous_transition.new_channel_communication)
qed

lemma sending_transition_from_adapted:
  assumes "S \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>A' \<triangleleft> \<star>\<^bsup>n\<^esup> X'\<rparr> T'"
  obtains A and X and T
    where
      "A' = A \<guillemotleft> \<E>"
    and
      "X' = X \<guillemotleft> on_suffix n \<E>"
    and
      "T' = T \<guillemotleft> on_suffix n \<E>"
    and
      "S \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> T"
using assms proof (induction "A' \<triangleleft> \<star>\<^bsup>n\<^esup> X'" "S \<guillemotleft> \<E>" T' arbitrary: A' n X' S \<E> thesis)
  case (sending A' X' S \<E>)
  from \<open>A' \<triangleleft> X' = S \<guillemotleft> \<E>\<close>
  obtain A and X where "A' = A \<guillemotleft> \<E>" and "X' = X \<guillemotleft> \<E>" and "S = A \<triangleleft> X"
    by (erule send_and_adapted)
  with sending(2) show ?case
    by
      (force
        simp only: identity_as_partial_on_suffix [symmetric] id_def adapted_after_stop
        intro: synchronous_transition.sending
      )
next
  case (scope_opening i n X' \<P>' A' Q' S \<E> thesis)
  from \<open>\<nu> a. \<P>' a = S \<guillemotleft> \<E>\<close> obtain \<P> where "\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)" and "S = \<nu> a. \<P> a"
    by (erule new_channel_and_adapted)
  from \<open>\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)\<close> have "\<nabla> \<P>' = \<nabla> \<P> \<guillemotleft> on_tail \<E>"
    unfolding on_tail_def
    by transfer (simp add: comp_def)
  with scope_opening(4)
  obtain B and Y and R
    where
      B_equation: "A' \<guillemotleft> tail = B \<guillemotleft> on_tail \<E>"
    and
      Y_equation: "X' \<guillemotleft> move n i = Y \<guillemotleft> on_suffix n (on_tail \<E>)"
    and
      R_equation: "Q' \<guillemotleft> move n i = R \<guillemotleft> on_suffix n (on_tail \<E>)"
    and
      "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>B \<triangleleft> \<star>\<^bsup>n\<^esup> Y\<rparr> R" .
  from B_equation obtain A where "A' = A \<guillemotleft> \<E>" and "B = A \<guillemotleft> tail"
    unfolding tail_def and on_tail_def
    by (blast elim: suffix_adapted_and_on_suffix_adapted)
  from Y_equation and R_equation
  have "X' \<guillemotleft> move n i = Y \<guillemotleft> on_suffix (Suc n) \<E>" and "Q' \<guillemotleft> move n i = R \<guillemotleft> on_suffix (Suc n) \<E>"
    using composition_as_partial_on_suffix [THEN fun_cong]
    by simp_all
  then obtain X and Q
    where
      "X' = X \<guillemotleft> on_suffix (Suc n) \<E>" and "Y = X \<guillemotleft> move n i"
    and
      "Q' = Q \<guillemotleft> on_suffix (Suc n) \<E>" and "R = Q \<guillemotleft> move n i"
    by (blast elim: move_adapted_and_on_suffix_adapted [OF lessI \<open>i \<le> n\<close> [THEN le_imp_less_Suc]])
  from \<open>i \<le> n\<close> and \<open>dependent_on_chan_at i X'\<close> have "dependent_on_chan_at i X"
    unfolding \<open>X' = X \<guillemotleft> on_suffix (Suc n) \<E>\<close>
    by (simp only: dependent_on_chan_at_after_on_suffix_adapted)
  with \<open>i \<le> n\<close> and \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>B \<triangleleft> \<star>\<^bsup>n\<^esup> Y\<rparr> R\<close> have "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>Suc n\<^esup> X\<rparr> Q"
    unfolding \<open>B = A \<guillemotleft> tail\<close> and \<open>Y = X \<guillemotleft> move n i\<close> and \<open>R = Q \<guillemotleft> move n i\<close>
    by (simp only: synchronous_transition.scope_opening)
  with
    \<open>A' = A \<guillemotleft> \<E>\<close>
  and
    \<open>X' = X \<guillemotleft> on_suffix (Suc n) \<E>\<close>
  and
    \<open>Q' = Q \<guillemotleft> on_suffix (Suc n) \<E>\<close>
  and
    scope_opening(6)
  show ?case
    unfolding \<open>S = \<nu> a. \<P> a\<close>
    by simp
next
  case (parallel_left_io P' A' n X' R' Q' S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close> obtain P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  from parallel_left_io(2) and \<open>P' = P \<guillemotleft> \<E>\<close>
  obtain A and X and R
    where
      "A' = A \<guillemotleft> \<E>"
    and
      "X' = X \<guillemotleft> on_suffix n \<E>"
    and
      "R' = R \<guillemotleft> on_suffix n \<E>"
    and
      "P \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> R" .
  from \<open>P \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> R\<close> have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> R \<parallel> Q \<guillemotleft> suffix n"
    by (fact synchronous_transition.parallel_left_io)
  moreover have "R' \<parallel> Q' \<guillemotleft> suffix n = (R \<parallel> Q \<guillemotleft> suffix n) \<guillemotleft> on_suffix n \<E>"
    unfolding \<open>Q' = Q \<guillemotleft> \<E>\<close> and \<open>R' = R \<guillemotleft> on_suffix n \<E>\<close>
    by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_on_suffix)
  ultimately show ?case
    using \<open>A' = A \<guillemotleft> \<E>\<close> and \<open>X' = X \<guillemotleft> on_suffix n \<E>\<close> and parallel_left_io(4)
    unfolding \<open>S = P \<parallel> Q\<close>
    by blast
next
  case (parallel_right_io Q' A' n X' R' P' S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close> obtain P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  from parallel_right_io(2) and \<open>Q' = Q \<guillemotleft> \<E>\<close>
  obtain A and X and R
    where
      "A' = A \<guillemotleft> \<E>"
    and
      "X' = X \<guillemotleft> on_suffix n \<E>"
    and
      "R' = R \<guillemotleft> on_suffix n \<E>"
    and
      "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> R" .
  from \<open>Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> R\<close> have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> P \<guillemotleft> suffix n \<parallel> R"
    by (fact synchronous_transition.parallel_right_io)
  moreover have "P' \<guillemotleft> suffix n \<parallel> R' = (P \<guillemotleft> suffix n \<parallel> R) \<guillemotleft> on_suffix n \<E>"
    unfolding \<open>P' = P \<guillemotleft> \<E>\<close> and \<open>R' = R \<guillemotleft> on_suffix n \<E>\<close>
    by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_on_suffix)
  ultimately show ?case
    using \<open>A' = A \<guillemotleft> \<E>\<close> and \<open>X' = X \<guillemotleft> on_suffix n \<E>\<close> and parallel_right_io(4)
    unfolding \<open>S = P \<parallel> Q\<close>
    by blast
next
  case (new_channel_io \<P>' A' n X' \<Q>' S \<E> thesis)
  from \<open>\<nu> a. \<P>' a = S \<guillemotleft> \<E>\<close> obtain \<P> where "\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)" and "S = \<nu> a. \<P> a"
    by (erule new_channel_and_adapted)
  from \<open>\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)\<close> have "\<nabla> \<P>' = \<nabla> \<P> \<guillemotleft> on_tail \<E>"
    unfolding on_tail_def
    by transfer (simp add: comp_def)
  with new_channel_io(2)
  obtain B and Y and R
    where
      B_equation: "A' \<guillemotleft> tail = B \<guillemotleft> on_tail \<E>"
    and
      Y_equation: "X' \<guillemotleft> remove n = Y \<guillemotleft> on_suffix n (on_tail \<E>)"
    and
      R_equation: "\<nabla>\<^bsub>n\<^esub> \<Q>' = R \<guillemotleft> on_suffix n (on_tail \<E>)"
    and
      "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>B \<triangleleft> \<star>\<^bsup>n\<^esup> Y\<rparr> R" .
  from B_equation obtain A where "A' = A \<guillemotleft> \<E>" and "B = A \<guillemotleft> tail"
    unfolding tail_def and on_tail_def
    by (blast elim: suffix_adapted_and_on_suffix_adapted)
  from Y_equation have "X' \<guillemotleft> remove n = Y \<guillemotleft> on_suffix (Suc n) \<E>"
    using composition_as_partial_on_suffix [THEN fun_cong]
    by simp
  then obtain X where "X' = X \<guillemotleft> on_suffix n \<E>" and "Y = X \<guillemotleft> remove n"
    by (blast elim: remove_adapted_and_on_suffix_adapted [OF le_refl])
  from R_equation have "\<nabla>\<^bsub>n\<^esub> \<Q>' = R \<guillemotleft> on_suffix (Suc n) \<E>"
    using composition_as_partial_on_suffix [THEN fun_cong]
    by simp
  then obtain \<Q> where "\<Q>' = (\<lambda>a. \<Q> a \<guillemotleft> on_suffix n \<E>)" and "R = \<nabla>\<^bsub>n\<^esub> \<Q>"
    by (blast elim: deep_uncurry_and_on_suffix_adapted [OF le_refl])
  from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>B \<triangleleft> \<star>\<^bsup>n\<^esup> Y\<rparr> R\<close> have \<open>\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> \<nu> a. \<Q> a\<close>
    unfolding \<open>B = A \<guillemotleft> tail\<close> and \<open>Y = X \<guillemotleft> remove n\<close> and \<open>R = \<nabla>\<^bsub>n\<^esub> \<Q>\<close>
    by (fact synchronous_transition.new_channel_io)
  moreover have "\<nu> a. \<Q>' a = (\<nu> a. \<Q> a) \<guillemotleft> on_suffix n \<E>"
    unfolding \<open>\<Q>' = (\<lambda>a. \<Q> a \<guillemotleft> on_suffix n \<E>)\<close>
    by (simp only: adapted_after_new_channel)
  ultimately show ?case
    using \<open>A' = A \<guillemotleft> \<E>\<close> and \<open>X' = X \<guillemotleft> on_suffix n \<E>\<close> and new_channel_io(4)
    unfolding \<open>S = \<nu> a. \<P> a\<close>
    by blast
qed

lemma receiving_transition_from_adapted:
  assumes "S \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>A' \<triangleright> \<star>\<^bsup>n\<^esup> X'\<rparr> T'"
  obtains A where "A' = A \<guillemotleft> \<E>"
using assms proof (induction "A' \<triangleright> \<star>\<^bsup>n\<^esup> X'" "S \<guillemotleft> \<E>" T' arbitrary: A' X' S \<E> thesis)
  case receiving
  then show ?case
    by (blast elim: receive_and_adapted)
next
  case (parallel_left_io P' A' X' R' Q' S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close> obtain P where "P' = P \<guillemotleft> \<E>"
    by (blast elim: parallel_and_adapted)
  with parallel_left_io(2,4) show ?case
    by blast
next
  case (parallel_right_io Q' A' X' R' P' S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close> obtain Q where "Q' = Q \<guillemotleft> \<E>"
    by (blast elim: parallel_and_adapted)
  with parallel_right_io(2,4) show ?case
    by blast
next
  case (new_channel_io \<P>' A' X' \<Q>' S \<E> thesis)
  from \<open>\<nu> a. \<P>' a = S \<guillemotleft> \<E>\<close> obtain \<P> where "\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)"
    by (blast elim: new_channel_and_adapted)
  then have "\<nabla> \<P>' = \<nabla> \<P> \<guillemotleft> on_tail \<E>"
    unfolding on_tail_def
    by transfer (simp add: comp_def)
  with new_channel_io(2) obtain B where "A' \<guillemotleft> tail = B \<guillemotleft> on_tail \<E>"
    by blast
  with new_channel_io(4) show ?case
    unfolding tail_def and on_tail_def
    by (blast elim: suffix_adapted_and_on_suffix_adapted)
qed

lemma adapted_receiving_transition_from_adapted:
  assumes "S \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> \<E> \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> on_suffix n \<E>\<rparr> T'"
  obtains T where "T' = T \<guillemotleft> on_suffix n \<E>" and "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T"
using assms proof (induction "A \<guillemotleft> \<E> \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> on_suffix n \<E>" "S \<guillemotleft> \<E>" T' arbitrary: A X S \<E> thesis)
  case (receiving \<P>' A X S \<E> thesis)
  from \<open>A \<guillemotleft> \<E> \<triangleright> x. \<P>' x = S \<guillemotleft> \<E>\<close>
  obtain \<P> where "\<P>' = (\<lambda>x. \<P> x \<guillemotleft> \<E>)" and "S = A \<triangleright> x. \<P> x"
    by (blast elim: receive_and_adapted)
  have "A \<triangleright> x. \<P> x \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e)"
    (is "_ \<rightarrow>\<^sub>s\<lparr>_\<rparr> ?Q")
    using synchronous_transition.receiving .
  moreover
  have "(\<lambda>d. (\<P>' ((X \<guillemotleft> on_suffix n \<E>) d) \<guillemotleft> suffix n) d) = ?Q \<guillemotleft> on_suffix n \<E>" (is "?R' = _")
  proof -
    have "?R' = (\<lambda>d. (\<P> ((X \<guillemotleft> on_suffix n \<E>) d) \<guillemotleft> \<E> \<guillemotleft> suffix n) d)"
      unfolding \<open>\<P>' = (\<lambda>x. \<P> x \<guillemotleft> \<E>)\<close>
      using refl .
    also have "\<dots> = (\<lambda>d. (\<P> ((X \<guillemotleft> on_suffix n \<E>) d) \<guillemotleft> suffix n \<guillemotleft> on_suffix n \<E>) d)"
      by (simp only: composition_adapted [symmetric] suffix_after_on_suffix)
    also have "\<dots> = ?Q \<guillemotleft> on_suffix n \<E>"
      by transfer (simp only: comp_def)
    finally show ?thesis .
  qed
  ultimately show ?case
    using receiving(2)
    unfolding \<open>S = A \<triangleright> x. \<P> x\<close>
    by simp
next
  case (parallel_left_io P' R' Q' A X S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close> obtain P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  from parallel_left_io(2) and \<open>P' = P \<guillemotleft> \<E>\<close>
  obtain R where "R' = R \<guillemotleft> on_suffix n \<E>" and "P \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> R"
    by blast
  from \<open>P \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> R\<close> have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> R \<parallel> Q \<guillemotleft> suffix n"
    by (fact synchronous_transition.parallel_left_io)
  moreover have "R' \<parallel> Q' \<guillemotleft> suffix n = (R \<parallel> Q \<guillemotleft> suffix n) \<guillemotleft> on_suffix n \<E>"
    unfolding \<open>Q' = Q \<guillemotleft> \<E>\<close> and \<open>R' = R \<guillemotleft> on_suffix n \<E>\<close>
    by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_on_suffix)
  ultimately show ?case
    using parallel_left_io(4)
    unfolding \<open>S = P \<parallel> Q\<close>
    by blast
next
  case (parallel_right_io Q' R' P' A X S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close> obtain P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  from parallel_right_io(2) and \<open>Q' = Q \<guillemotleft> \<E>\<close>
  obtain R where "R' = R \<guillemotleft> on_suffix n \<E>" and "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> R"
    by blast
  from \<open>Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> R\<close> have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> P \<guillemotleft> suffix n \<parallel> R"
    by (fact synchronous_transition.parallel_right_io)
  moreover have "P' \<guillemotleft> suffix n \<parallel> R' = (P \<guillemotleft> suffix n \<parallel> R) \<guillemotleft> on_suffix n \<E>"
    unfolding \<open>P' = P \<guillemotleft> \<E>\<close> and \<open>R' = R \<guillemotleft> on_suffix n \<E>\<close>
    by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_on_suffix)
  ultimately show ?case
    using parallel_right_io(4)
    unfolding \<open>S = P \<parallel> Q\<close>
    by blast
next
  case (new_channel_io \<P>' \<Q>' A X S \<E> thesis)
  from \<open>\<nu> a. \<P>' a = S \<guillemotleft> \<E>\<close> obtain \<P> where "\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)" and "S = \<nu> a. \<P> a"
    by (erule new_channel_and_adapted)
  from \<open>\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)\<close> have "\<nabla> \<P>' = \<nabla> \<P> \<guillemotleft> on_tail \<E>"
    unfolding on_tail_def
    by transfer (simp add: comp_def)
  moreover have "A \<guillemotleft> \<E> \<guillemotleft> tail = A \<guillemotleft> tail \<guillemotleft> on_tail \<E>"
    unfolding tail_def and on_tail_def
    by (simp only: composition_adapted [symmetric] suffix_after_on_suffix)
  moreover have "X \<guillemotleft> on_suffix n \<E> \<guillemotleft> remove n = X \<guillemotleft> remove n \<guillemotleft> on_suffix n (on_tail \<E>)"
  proof -
    have "X \<guillemotleft> on_suffix n \<E> \<guillemotleft> remove n = X \<guillemotleft> remove n \<guillemotleft> on_suffix (Suc n) \<E>"
      by (simp only: composition_adapted [symmetric] remove_after_on_suffix)
    also have "\<dots> = X \<guillemotleft> remove n \<guillemotleft> on_suffix n (on_tail \<E>)"
      using composition_as_partial_on_suffix [THEN fun_cong]
      by simp
    finally show ?thesis .
  qed
  ultimately obtain R
    where "\<nabla>\<^bsub>n\<^esub> \<Q>' = R \<guillemotleft> on_suffix n (on_tail \<E>)" and "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> remove n\<rparr> R"
    using new_channel_io(2)
    by blast
  from this(1) have "\<nabla>\<^bsub>n\<^esub> \<Q>' = R \<guillemotleft> on_suffix (Suc n) \<E>"
    using composition_as_partial_on_suffix [THEN fun_cong]
    by simp
  then obtain \<Q> where "\<Q>' = (\<lambda>a. \<Q> a \<guillemotleft> on_suffix n \<E>)" and "R = \<nabla>\<^bsub>n\<^esub> \<Q>"
    by (blast elim: deep_uncurry_and_on_suffix_adapted [OF le_refl])
  from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> remove n\<rparr> R\<close> have \<open>\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> \<nu> a. \<Q> a\<close>
    unfolding \<open>R = \<nabla>\<^bsub>n\<^esub> \<Q>\<close>
    by (fact synchronous_transition.new_channel_io)
  moreover have "\<nu> a. \<Q>' a = (\<nu> a. \<Q> a) \<guillemotleft> on_suffix n \<E>"
    unfolding \<open>\<Q>' = (\<lambda>a. \<Q> a \<guillemotleft> on_suffix n \<E>)\<close>
    by (simp only: adapted_after_new_channel)
  ultimately show ?case
    using new_channel_io(4)
    unfolding \<open>S = \<nu> a. \<P> a\<close>
    by blast
qed

lemma communication_transition_from_adapted:
  assumes "S \<guillemotleft> \<E> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> T'"
  obtains T where "T' = T \<guillemotleft> \<E>" and "S \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> T"
using assms proof (induction \<tau> "S \<guillemotleft> \<E>" T' arbitrary: S \<E> thesis)
  case (communication \<eta> \<mu> P' A' n X' R' Q' U' S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close>
  obtain P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  obtain A and X and R and U
    where
      "R' = R \<guillemotleft> on_suffix n \<E>"
    and
      "U' = U \<guillemotleft> on_suffix n \<E>"
    and
      "P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> R"
    and
      "Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> U"
  proof (cases \<eta>)
    case Sending
    from \<open>\<eta> \<noteq> \<mu>\<close> and \<open>\<eta> = Sending\<close> have "\<mu> = Receiving"
      by (cases \<mu>) simp
    from \<open>P' \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X'\<rparr> R'\<close>
    obtain A and X and R
      where
        "A' = A \<guillemotleft> \<E>"
      and
        "X' = X \<guillemotleft> on_suffix n \<E>"
      and
        "R' = R \<guillemotleft> on_suffix n \<E>"
      and
        "P \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> R"
      unfolding \<open>P' = P \<guillemotleft> \<E>\<close> and \<open>\<eta> = Sending\<close>
      by (erule sending_transition_from_adapted)
    from \<open>Q' \<rightarrow>\<^sub>s\<lparr>IO \<mu> A' n X'\<rparr> U'\<close>
    obtain U where "U' = U \<guillemotleft> on_suffix n \<E>" and "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> U"
      unfolding
        \<open>Q' = Q \<guillemotleft> \<E>\<close>
      and
        \<open>\<mu> = Receiving\<close>
      and
        \<open>A' = A \<guillemotleft> \<E>\<close>
      and
        \<open>X' = X \<guillemotleft> on_suffix n \<E>\<close>
      by (erule adapted_receiving_transition_from_adapted)
    with \<open>R' = R \<guillemotleft> on_suffix n \<E>\<close> and \<open>P \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> R\<close> show ?thesis
      using that
      unfolding \<open>\<eta> = Sending\<close> and \<open>\<mu> = Receiving\<close>
      by simp
  next
    case Receiving
    from \<open>\<eta> \<noteq> \<mu>\<close> and \<open>\<eta> = Receiving\<close> have "\<mu> = Sending"
      by (cases \<mu>) simp_all
    from \<open>Q' \<rightarrow>\<^sub>s\<lparr>IO \<mu> A' n X'\<rparr> U'\<close>
    obtain A and X and U
      where
        "A' = A \<guillemotleft> \<E>"
      and
        "X' = X \<guillemotleft> on_suffix n \<E>"
      and
        "U' = U \<guillemotleft> on_suffix n \<E>"
      and
        "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> U"
      unfolding \<open>Q' = Q \<guillemotleft> \<E>\<close> and \<open>\<mu> = Sending\<close>
      by (erule sending_transition_from_adapted)
    from \<open>P' \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X'\<rparr> R'\<close>
    obtain R where "R' = R \<guillemotleft> on_suffix n \<E>" and "P \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> R"
      unfolding
        \<open>P' = P \<guillemotleft> \<E>\<close>
      and
        \<open>\<eta> = Receiving\<close>
      and
        \<open>A' = A \<guillemotleft> \<E>\<close>
      and
        \<open>X' = X \<guillemotleft> on_suffix n \<E>\<close>
      by (erule adapted_receiving_transition_from_adapted)
    with \<open>U' = U \<guillemotleft> on_suffix n \<E>\<close> and \<open>Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> U\<close> show ?thesis
      using that
      unfolding \<open>\<eta> = Receiving\<close> and \<open>\<mu> = Sending\<close>
      by simp
  qed
  from \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> R\<close> and \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> U\<close> have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (R \<parallel> U)"
    using \<open>\<eta> \<noteq> \<mu>\<close>
    by (blast intro: synchronous_transition.communication)
  moreover have "\<star>\<^bsup>n\<^esup> (R' \<parallel> U') = \<star>\<^bsup>n\<^esup> (R \<parallel> U) \<guillemotleft> \<E>"
    unfolding \<open>R' = R \<guillemotleft> on_suffix n \<E>\<close> and \<open>U' = U \<guillemotleft> on_suffix n \<E>\<close>
    by (simp only: adapted_after_create_channel_power adapted_after_parallel)
  ultimately show ?case
    using communication(5)
    unfolding \<open>S = P \<parallel> Q\<close>
    by simp
next
  case (parallel_left_communication P' R' Q' S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close>
  obtain P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  from parallel_left_communication(2) and \<open>P' = P \<guillemotleft> \<E>\<close>
  obtain R where "R' = R \<guillemotleft> \<E>" and "P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R" .
  from \<open>P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R\<close> have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R \<parallel> Q"
    by (fact synchronous_transition.parallel_left_communication)
  moreover have "R' \<parallel> Q' = (R \<parallel> Q) \<guillemotleft> \<E>"
    unfolding \<open>Q' = Q \<guillemotleft> \<E>\<close> and \<open>R' = R \<guillemotleft> \<E>\<close>
    by (simp only: adapted_after_parallel)
  ultimately show ?case
    using parallel_left_communication(4)
    unfolding \<open>S = P \<parallel> Q\<close>
    by blast
next
  case (parallel_right_communication Q' R' P' S \<E> thesis)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> \<E>\<close>
  obtain P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  from parallel_right_communication(2) and \<open>Q' = Q \<guillemotleft> \<E>\<close>
  obtain R where "R' = R \<guillemotleft> \<E>" and "Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R" .
  from \<open>Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R\<close> have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P \<parallel> R"
    by (fact synchronous_transition.parallel_right_communication)
  moreover have "P' \<parallel> R' = (P \<parallel> R) \<guillemotleft> \<E>"
    unfolding \<open>P' = P \<guillemotleft> \<E>\<close> and \<open>R' = R \<guillemotleft> \<E>\<close>
    by (simp only: adapted_after_parallel)
  ultimately show ?case
    using parallel_right_communication(4)
    unfolding \<open>S = P \<parallel> Q\<close>
    by blast
next
  case (new_channel_communication \<P>' \<Q>' S \<E> thesis)
  from \<open>\<nu> a. \<P>' a = S \<guillemotleft> \<E>\<close> obtain \<P> where "\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)" and "S = \<nu> a. \<P> a"
    by (erule new_channel_and_adapted)
  from \<open>\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)\<close> have "\<nabla> \<P>' = \<nabla> \<P> \<guillemotleft> on_tail \<E>"
    unfolding on_tail_def
    by transfer (simp add: comp_def)
  with new_channel_communication(2) obtain R where "\<nabla> \<Q>' = R \<guillemotleft> on_tail \<E>" and "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R" .
  from \<open>\<nabla> \<Q>' = R \<guillemotleft> on_tail \<E>\<close> obtain \<Q> where "\<Q>' = (\<lambda>a. \<Q> a \<guillemotleft> \<E>)" and "R = \<nabla> \<Q>"
    by
      (auto
        elim: family_uncurry_and_on_suffix_adapted [simplified]
        simp add: identity_as_partial_on_suffix [symmetric]
      )
  from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R\<close> have \<open>\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nu> a. \<Q> a\<close>
    unfolding \<open>R = \<nabla> \<Q>\<close>
    by (fact synchronous_transition.new_channel_communication)
  moreover have "\<nu> a. \<Q>' a = (\<nu> a. \<Q> a) \<guillemotleft> \<E>"
    unfolding \<open>\<Q>' = (\<lambda>a. \<Q> a \<guillemotleft> \<E>)\<close>
    by (simp only: adapted_after_new_channel)
  ultimately show ?case
    using new_channel_communication(4)
    unfolding \<open>S = \<nu> a. \<P> a\<close>
    by blast
qed

context begin

private lemma successor_suffix_via_remove_and_move:
  shows "suffix (Suc n) = remove i \<bullet> suffix n \<bullet> move n (n + i)"
proof -
  have "suffix (Suc n) = remove 0 \<bullet> suffix n"
    by transfer auto
  also have "\<dots> = remove i \<bullet> move 0 i \<bullet> suffix n"
    by transfer (simp only: comp_def delete_at_after_insert_at)
  also have "\<dots> = remove i \<bullet> suffix n \<bullet> move n (n + i)"
    by (simp add: adaptation_composition_associativity move_after_suffix)
  finally show ?thesis .
qed

text \<open>
  In the following, \<^theory_text>\<open>receiving\<close> refers to the rule, not to the kind of I/O.
\<close>

private lemma move_adapted_receiving_target_production:
  shows "
    (\<lambda>e. (\<P> ((X \<guillemotleft> move n (n + i)) e) \<guillemotleft> suffix (Suc n)) e)
    =
    (\<lambda>d. (\<P> (X d) \<guillemotleft> remove i \<guillemotleft> suffix n) d) \<guillemotleft> move n (n + i)"
    (is "?Q = ?R")
proof -
  have "?Q = (\<lambda>e. (\<P> ((X \<guillemotleft> move n (n + i)) e) \<guillemotleft> remove i \<guillemotleft> suffix n \<guillemotleft> move n (n + i)) e)"
    by (simp only: successor_suffix_via_remove_and_move [where i = i] composition_adapted)
  also have "\<dots> = ?R"
    by transfer (simp only: comp_def)
  finally show ?thesis .
qed

private lemma move_adapted_new_channel_io_inner_value_production:
  shows "X \<guillemotleft> move n (n + i) \<guillemotleft> remove (Suc n) = X \<guillemotleft> remove n \<guillemotleft> move n (n + Suc i)"
  by
    transfer
    (simp
      del: stake.simps(2) sdrop.simps(2)
      add: comp_def stake_shift sdrop_shift take_stake drop_stake min_absorb2 min_absorb1
    )

private lemma move_adapted_new_channel_io_inner_target_production:
  shows "\<nabla>\<^bsub>Suc n\<^esub> (\<lambda>a. \<Q> a \<guillemotleft> move n (n + i)) = \<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> move n (n + Suc i)"
  by
    transfer
    (
      simp
        del: stake.simps(2) sdrop.simps(2)
        add: comp_def stake_shift sdrop_shift take_stake drop_stake min_absorb2 min_absorb1,
      simp
    )

private lemma receiving_transition_with_remove_adapted_source_part_forward_rule:
  assumes "S \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove i \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T"
  shows "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr> T \<guillemotleft> move n (n + i)"
using assms proof (induction "A \<guillemotleft> remove i \<triangleright> \<star>\<^bsup>n\<^esup> X" "S \<guillemotleft> remove i" T arbitrary: A i X S)
  case (receiving \<P>' X A i S)
  from \<open>A \<guillemotleft> remove i \<triangleright> x. \<P>' x = S \<guillemotleft> remove i\<close>
  obtain \<P> where "\<P>' = (\<lambda>x. \<P> x \<guillemotleft> remove i)" and "S = A \<triangleright> x. \<P> x"
    by (blast elim: receive_and_adapted)
  have "
    A \<triangleright> x. \<P> x
    \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr>
    (\<lambda>e. (\<P> ((X \<guillemotleft> move n (n + i)) e) \<guillemotleft> suffix (Suc n)) e)"
    (is "_ \<rightarrow>\<^sub>s\<lparr>_\<rparr> ?Q")
    using synchronous_transition.receiving .
  moreover have "?Q = (\<lambda>d. (\<P>' (X d) \<guillemotleft> suffix n) d) \<guillemotleft> move n (n + i)"
    unfolding \<open>\<P>' = (\<lambda>x. \<P> x \<guillemotleft> remove i)\<close>
    using move_adapted_receiving_target_production .
  ultimately show ?case
    unfolding \<open>S = A \<triangleright> x. \<P> x\<close>
    by simp
next
  case (parallel_left_io P' X R Q' A i S)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> remove i\<close>
  obtain P and Q where "P' = P \<guillemotleft> remove i" and "Q' = Q \<guillemotleft> remove i" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  from parallel_left_io(2) and \<open>P' = P \<guillemotleft> remove i\<close>
  have "P \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr> R \<guillemotleft> move n (n + i)"
    by simp
  then have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr> R \<guillemotleft> move n (n + i) \<parallel> Q \<guillemotleft> suffix (Suc n)"
    (is "_ \<rightarrow>\<^sub>s\<lparr>_\<rparr> ?U")
    by (fact synchronous_transition.parallel_left_io)
  moreover have "?U = (R \<parallel> Q' \<guillemotleft> suffix n) \<guillemotleft> move n (n + i)"
    unfolding \<open>Q' = Q \<guillemotleft> remove i\<close>
    by
      (simp only:
        successor_suffix_via_remove_and_move [where i = i]
        composition_adapted
        adapted_after_parallel
      )
  ultimately show ?case
    unfolding \<open>S = P \<parallel> Q\<close>
    by simp
next
  case (parallel_right_io Q' X R P' A i S)
  from \<open>P' \<parallel> Q' = S \<guillemotleft> remove i\<close>
  obtain P and Q where "P' = P \<guillemotleft> remove i" and "Q' = Q \<guillemotleft> remove i" and "S = P \<parallel> Q"
    by (erule parallel_and_adapted)
  from parallel_right_io(2) and \<open>Q' = Q \<guillemotleft> remove i\<close>
  have "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr> R \<guillemotleft> move n (n + i)"
    by simp
  then have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr> P \<guillemotleft> suffix (Suc n) \<parallel> R \<guillemotleft> move n (n + i)"
    (is "_ \<rightarrow>\<^sub>s\<lparr>_\<rparr> ?U")
    by (fact synchronous_transition.parallel_right_io)
  moreover have "?U = (P' \<guillemotleft> suffix n \<parallel> R) \<guillemotleft> move n (n + i)"
    unfolding \<open>P' = P \<guillemotleft> remove i\<close>
    by
      (simp only:
        successor_suffix_via_remove_and_move [where i = i]
        composition_adapted
        adapted_after_parallel
      )
  ultimately show ?case
    unfolding \<open>S = P \<parallel> Q\<close>
    by simp
next
  case (new_channel_io \<P>' X \<Q> A i S)
  from \<open>\<nu> a. \<P>' a = S \<guillemotleft> remove i\<close> obtain \<P> where "\<P>' = (\<lambda>a. \<P> a \<guillemotleft> remove i)" and "S = \<nu> a. \<P> a"
    by (erule new_channel_and_adapted)
  from \<open>\<P>' = (\<lambda>a. \<P> a \<guillemotleft> remove i)\<close> have "\<nabla> \<P>' = \<nabla> \<P> \<guillemotleft> remove (Suc i)"
    by (simp only: remove_adapted_after_family_uncurry)
  moreover have "A \<guillemotleft> remove i \<guillemotleft> tail = A \<guillemotleft> tail \<guillemotleft> remove (Suc i)"
    unfolding tail_def
    by (simp add: composition_adapted [symmetric] remove_after_suffix)
  ultimately have
    "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> remove n \<guillemotleft> move n (n + Suc i)\<rparr> \<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> move n (n + Suc i)"
    using new_channel_io(2)
    by blast
  then have "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr> \<nu> a. \<Q> a \<guillemotleft> move n (n + i)"
    unfolding
      move_adapted_new_channel_io_inner_value_production [symmetric]
    and
      move_adapted_new_channel_io_inner_target_production [symmetric]
    by (intro synchronous_transition.new_channel_io)
  moreover have "\<nu> a. \<Q> a \<guillemotleft> move n (n + i) = (\<nu> a. \<Q> a) \<guillemotleft> move n (n + i)"
    by (simp only: adapted_after_new_channel)
  ultimately show ?case
    unfolding \<open>S = \<nu> a. \<P> a\<close>
    by simp
qed

private lemma receiving_transition_with_remove_adapted_source_part_backward_rule:
  assumes "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr> T \<guillemotleft> move n (n + i)"
  shows "S \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove i \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T"
using assms
proof (induction "A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)" S "T \<guillemotleft> move n (n + i)" arbitrary: A X i T)
  case (receiving A \<P> X i T)
  then have "T = (\<lambda>a. (\<P> (X a) \<guillemotleft> remove i \<guillemotleft> suffix n) a)"
    by (simp add: move_adapted_receiving_target_production)
  then show ?case
    by (auto simp only: adapted_after_receive intro: synchronous_transition.receiving)
next
  case (parallel_left_io P A R' Q X i T)
  from \<open>R' \<parallel> Q \<guillemotleft> suffix (Suc n) = T \<guillemotleft> move n (n + i)\<close>
  obtain R and U
    where "R' = R \<guillemotleft> move n (n + i)" and "Q \<guillemotleft> suffix (Suc n) = U \<guillemotleft> move n (n + i)" and "T = R \<parallel> U"
    by (erule parallel_and_adapted)
  from parallel_left_io(2) and \<open>R' = R \<guillemotleft> move n (n + i)\<close>
  have "P \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove i \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> R"
    by simp
  moreover from \<open>Q \<guillemotleft> suffix (Suc n) = U \<guillemotleft> move n (n + i)\<close> have "U = Q \<guillemotleft> remove i \<guillemotleft> suffix n"
    by (simp add: successor_suffix_via_remove_and_move [where i = i] composition_adapted)
  ultimately show ?case
    unfolding \<open>T = R \<parallel> U\<close>
    by (simp only: adapted_after_parallel synchronous_transition.parallel_left_io)
next
  case (parallel_right_io Q A R' P X i T)
  from \<open>P \<guillemotleft> suffix (Suc n) \<parallel> R' = T \<guillemotleft> move n (n + i)\<close>
  obtain R and U
    where "P \<guillemotleft> suffix (Suc n) = U \<guillemotleft> move n (n + i)" and "R' = R \<guillemotleft> move n (n + i)" and "T = U \<parallel> R"
    by (erule parallel_and_adapted)
  from parallel_right_io(2) and \<open>R' = R \<guillemotleft> move n (n + i)\<close>
  have "Q \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove i \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> R"
    by simp
  moreover from \<open>P \<guillemotleft> suffix (Suc n) = U \<guillemotleft> move n (n + i)\<close> have "U = P \<guillemotleft> remove i \<guillemotleft> suffix n"
    by (simp add: successor_suffix_via_remove_and_move [where i = i] composition_adapted)
  ultimately show ?case
    unfolding \<open>T = U \<parallel> R\<close>
    by (simp only: adapted_after_parallel synchronous_transition.parallel_right_io)
next
  case (new_channel_io \<P> A \<Q>' X i T)
  from \<open>\<nu> a. \<Q>' a = T \<guillemotleft> move n (n + i)\<close>
  obtain \<Q> where "\<Q>' = (\<lambda>a. \<Q> a \<guillemotleft> move n (n + i))" and "T = \<nu> a. \<Q> a"
    by (erule new_channel_and_adapted)
  from new_channel_io(2)
  have "\<nabla> \<P> \<guillemotleft> remove (Suc i) \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<guillemotleft> remove (Suc i) \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> remove n\<rparr> \<nabla>\<^bsub>n\<^esub> \<Q>"
    unfolding \<open>\<Q>' = (\<lambda>a. \<Q> a \<guillemotleft> move n (n + i))\<close>
    using
      move_adapted_new_channel_io_inner_value_production
    and
      move_adapted_new_channel_io_inner_target_production .
  moreover have "\<nabla> \<P> \<guillemotleft> remove (Suc i) = \<nabla> (\<lambda>a. \<P> a \<guillemotleft> remove i)"
    by transfer (simp add: comp_def)
  moreover have "A \<guillemotleft> tail \<guillemotleft> remove (Suc i) = A \<guillemotleft> remove i \<guillemotleft> tail"
    unfolding tail_def
    by transfer (simp add: comp_def)
  ultimately show ?case
    unfolding \<open>T = \<nu> a. \<Q> a\<close>
    by (simp only: adapted_after_new_channel synchronous_transition.new_channel_io)
qed

lemma receiving_transition_with_remove_adapted_source_part:
  shows "
    S \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove i \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T
    \<longleftrightarrow>
    S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i)\<rparr> T \<guillemotleft> move n (n + i)"
  using
    receiving_transition_with_remove_adapted_source_part_forward_rule
  and
    receiving_transition_with_remove_adapted_source_part_backward_rule
  ..

end

context begin

private lemma receiving_transition_with_move_adapted_target_part_backward_rule:
  assumes "i < n" and "j < n" and "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T"
  shows "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move i j\<rparr> T \<guillemotleft> move i j"
using \<open>S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T\<close> proof (induction "A \<triangleright> \<star>\<^bsup>n\<^esup> X" S T arbitrary: A X)
  case (receiving A \<P> X)
  have
    "A \<triangleright> x. \<P> x \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move i j\<rparr> (\<lambda>e. (\<P> ((X \<guillemotleft> move i j) e) \<guillemotleft> suffix n) e)"
    (is "_ \<rightarrow>\<^sub>s\<lparr>_\<rparr> ?Q")
    using synchronous_transition.receiving .
  moreover
  have "?Q = (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e) \<guillemotleft> move i j"
  proof -
    from \<open>i < n\<close> and \<open>j < n\<close> have "?Q = (\<lambda>e. (\<P> ((X \<guillemotleft> move i j) e) \<guillemotleft> suffix n \<guillemotleft> move i j) e)"
      by (simp only: composition_adapted [symmetric] suffix_after_move)
    also have "\<dots> = (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e) \<guillemotleft> move i j"
      by transfer (simp only: comp_def)
    finally show ?thesis .
  qed
  ultimately show ?case
    by (simp only:)
next
  case (parallel_left_io P A X R Q)
  from parallel_left_io(2) have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move i j\<rparr> R \<guillemotleft> move i j \<parallel> Q \<guillemotleft> suffix n"
    by (fact synchronous_transition.parallel_left_io)
  with \<open>i < n\<close> and \<open>j < n\<close> show ?case
    by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_move)
next
  case (parallel_right_io Q A X R P)
  from parallel_right_io(2) have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move i j\<rparr> P \<guillemotleft> suffix n \<parallel> R \<guillemotleft> move i j"
    by (fact synchronous_transition.parallel_right_io)
  with \<open>i < n\<close> and \<open>j < n\<close> show ?case
    by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_move)
next
  case (new_channel_io \<P> A X \<Q>)
  from new_channel_io(2)
  have "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> remove n \<guillemotleft> move i j\<rparr> \<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> move i j" .
  moreover
  have "X \<guillemotleft> remove n \<guillemotleft> move i j = X \<guillemotleft> move i j \<guillemotleft> remove n"
    using \<open>i < n\<close> and \<open>j < n\<close>
    by (simp only: composition_adapted [symmetric] move_after_backyard_remove)
  moreover
  have "\<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> move i j = \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<Q> a \<guillemotleft> move i j)"
    using \<open>i < n\<close> and \<open>j < n\<close>
    by (simp only: move_adapted_after_deeper_uncurry)
  ultimately show ?case
    by (simp only: synchronous_transition.new_channel_io adapted_after_new_channel)
qed

lemma receiving_transition_with_move_adapted_target_part:
  assumes "i < n" and "j < n"
  shows "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move i j\<rparr> T \<guillemotleft> move i j \<longleftrightarrow> S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T"
proof
  assume "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move i j\<rparr> T \<guillemotleft> move i j"
  then have "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move i j \<guillemotleft> move j i\<rparr> T \<guillemotleft> move i j \<guillemotleft> move j i"
    using assms
    by (blast intro: receiving_transition_with_move_adapted_target_part_backward_rule)
  then show "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T"
    by (simp only: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
next
  assume "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X\<rparr> T"
  then show "S \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move i j\<rparr> T \<guillemotleft> move i j"
    using assms
    by (intro receiving_transition_with_move_adapted_target_part_backward_rule)
qed

end

interpretation synchronous: transition_system \<open>synchronous_transition\<close> .

notation synchronous.bisimilarity (infix \<open>\<sim>\<^sub>s\<close> 50)
notation synchronous.constant_bisimilarity (\<open>[\<sim>\<^sub>s]\<close>)
notation synchronous.simulation_up_to (\<open>sync'_sim\<^bsub>_\<^esub>\<close>)

interpretation synchronous: weak_transition_system \<open>synchronous_transition\<close> \<open>\<tau>\<close> .

notation synchronous.weak_transition (\<open>'(\<Rightarrow>\<^sub>s\<lparr>_\<rparr>')\<close>)
notation synchronous.weak_transition_std (\<open>(_ \<Rightarrow>\<^sub>s\<lparr>_\<rparr>/ _)\<close> [51, 0, 51] 50)

notation synchronous.weak.bisimilarity (infix \<open>\<approx>\<^sub>s\<close> 50)
notation synchronous.weak.constant_bisimilarity (\<open>[\<approx>\<^sub>s]\<close>)
notation synchronous.weak.simulation_up_to (\<open>sync'_weak'_sim\<^bsub>_\<^esub>\<close>)

notation synchronous.mixed.bisimilarity (infix \<open>\<asymp>\<^sub>s\<close> 50)
notation synchronous.mixed.constant_bisimilarity (\<open>[\<asymp>\<^sub>s]\<close>)
notation synchronous.mixed.simulation_up_to (\<open>sync'_mixed'_sim\<^bsub>_\<^esub>\<close>)

definition
  synchronous_shortcut_transition :: "action option \<Rightarrow> process family relation"
  (\<open>'(\<rightarrow>\<^sub>s\<^sup>?\<lparr>_\<rparr>')\<close>)
where
  [simp]: "synchronous_shortcut_transition = with_shortcut synchronous_transition"
(* FIXME: Make sure that the superscript is put above the subscript in the PDF output. *)

abbreviation
  synchronous_shortcut_transition_std :: "
    process family \<Rightarrow>
    action option \<Rightarrow>
    process family \<Rightarrow>
    bool"
  (\<open>(_ \<rightarrow>\<^sub>s\<^sup>?\<lparr>_\<rparr>/ _)\<close> [51, 0, 51] 50) where
  "P \<rightarrow>\<^sub>s\<^sup>?\<lparr>\<alpha>\<rparr> Q \<equiv> (\<rightarrow>\<^sub>s\<^sup>?\<lparr>\<alpha>\<rparr>) P Q"
(* FIXME: Make sure that the superscript is put above the subscript in the PDF output. *)

definition parallel_mutation :: "process family \<Rightarrow> process family relation" (\<open>{_ \<parallel> \<hole>}\<close> [51]) where
  [simp]: "{P \<parallel> \<hole>} Q S \<longleftrightarrow> S = P \<parallel> Q"

definition create_channel_mutation :: "process family relation" (\<open>{\<star> \<hole>}\<close>) where
  [simp]: "{\<star> \<hole>} P S \<longleftrightarrow> S = \<star> P"

lemma create_channel_mutation_power_def [simp]:
  shows "{\<star> \<hole>}\<^bsup>n\<^esup> P S \<longleftrightarrow> S = \<star>\<^bsup>n\<^esup> P"
  by (induction n arbitrary: S) auto

definition adapted_mutation :: "adaptation \<Rightarrow> process family relation" (\<open>{\<hole> \<guillemotleft> _}\<close> [56]) where
  [simp]: "{\<hole> \<guillemotleft> \<E>} P S \<longleftrightarrow> S = P \<guillemotleft> \<E>"

inductive_set universe :: "process family relation set" (\<open>\<U>\<close>) where
  parallel_mutation_in_universe:
    "{P \<parallel> \<hole>} \<in> \<U>" |
  create_channel_mutation_in_universe:
    "{\<star> \<hole>} \<in> \<U>" |
  remove_adapted_mutation_in_universe:
    "{\<hole> \<guillemotleft> remove i} \<in> \<U>" |
  injectively_adapted_mutation_in_universe:
    "{\<hole> \<guillemotleft> \<E>} \<in> \<U>"
    if "injective \<E>" |
  composition_in_universe:
    "I OO J \<in> \<U>"
    if "I \<in> \<U>" and "J \<in> \<U>"

lemma suffix_adapted_mutation_in_universe:
  shows "{\<hole> \<guillemotleft> suffix n} \<in> \<U>"
proof (induction n)
  case 0
  have "{\<hole> \<guillemotleft> suffix 0} = {\<hole> \<guillemotleft> \<one>}"
    by (rule arg_cong) (transfer, auto)
  also have "{\<hole> \<guillemotleft> \<one>} \<in> \<U>"
    by (simp only: identity_is_injective injectively_adapted_mutation_in_universe)
  finally show ?case .
next
  case (Suc n)
  have "{\<hole> \<guillemotleft> suffix (Suc n)} = {\<hole> \<guillemotleft> (remove 0 \<bullet> suffix n)}"
    by (rule arg_cong) (transfer, auto)
  also have "\<dots> = {\<hole> \<guillemotleft> remove 0} OO {\<hole> \<guillemotleft> suffix n}"
    by (fastforce simp add: composition_adapted)
  also have "\<dots> \<in> \<U>"
    using Suc.IH
    by (blast intro: remove_adapted_mutation_in_universe composition_in_universe)
  finally show ?case .
qed

lemma equality_in_universe:
  shows "(=) \<in> \<U>"
proof -
  have "(=) = {\<hole> \<guillemotleft> \<one>}"
    by (fastforce simp add: identity_adapted)
  also have "\<dots> \<in> \<U>"
  by (simp only: identity_is_injective injectively_adapted_mutation_in_universe)
  finally show ?thesis .
qed

lemma power_in_universe:
  assumes "I \<in> \<U>"
  shows "I\<^bsup>n\<^esup> \<in> \<U>"
  using assms
  by (induction n) (simp_all add: equality_in_universe composition_in_universe)

inductive
  synchronous_mutation_transition_std :: "
    process family relation \<Rightarrow>
    action \<Rightarrow>
    action option \<Rightarrow>
    process family relation \<Rightarrow>
    bool"
  (\<open>(_ \<longrightarrow>\<^sub>s\<lparr>_ \<bar> _\<rparr>/ _)\<close> [51, 0, 0, 51] 50)
where
  \<comment> \<open>\<^term>\<open>{P \<parallel> \<hole>}\<close>:\<close>
  mutation_communication:
    "{P \<parallel> \<hole>} \<longrightarrow>\<^sub>s\<lparr>\<tau> \<bar> Some (IO \<mu> A n X)\<rparr> {P' \<parallel> \<hole>} OO {\<star> \<hole>}\<^bsup>n\<^esup>"
    if "\<eta> \<noteq> \<mu>" and "P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'" |
  mutation_parallel_left_io:
    "{P \<parallel> \<hole>} \<longrightarrow>\<^sub>s\<lparr>IO \<eta> A n X \<bar> None\<rparr> {\<hole> \<guillemotleft> suffix n} OO {P' \<parallel> \<hole>}"
    if "P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'" |
  mutation_parallel_left_communication:
    "{P \<parallel> \<hole>} \<longrightarrow>\<^sub>s\<lparr>\<tau> \<bar> None\<rparr> {P' \<parallel> \<hole>}"
    if "P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'" |
  mutation_parallel_right_io:
    "{P \<parallel> \<hole>} \<longrightarrow>\<^sub>s\<lparr>IO \<eta> A n X \<bar> Some (IO \<eta> A n X)\<rparr> {P \<guillemotleft> suffix n \<parallel> \<hole>}" |
  mutation_parallel_right_communication:
    "{P \<parallel> \<hole>} \<longrightarrow>\<^sub>s\<lparr>\<tau> \<bar> Some \<tau>\<rparr> {P \<parallel> \<hole>}" |
  \<comment> \<open>\<^term>\<open>{\<star> \<hole>}\<close>:\<close>
  mutation_scope_opening:
    "{\<star> \<hole>} \<longrightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>Suc n\<^esup> X \<bar> Some (A \<guillemotleft> tail \<triangleleft> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move n i)\<rparr> {\<hole> \<guillemotleft> move i n}"
    if "i \<le> n" and "dependent_on_chan_at i X" |
  mutation_new_channel_io:
    "{\<star> \<hole>} \<longrightarrow>\<^sub>s\<lparr>IO \<eta> A n X \<bar> Some (IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n))\<rparr> {\<hole> \<guillemotleft> move 0 n} OO {\<star> \<hole>}" |
  mutation_new_channel_communication:
    "{\<star> \<hole>} \<longrightarrow>\<^sub>s\<lparr>\<tau> \<bar> Some \<tau>\<rparr> {\<star> \<hole>}" |
  \<comment> \<open>\<^term>\<open>{\<hole> \<guillemotleft> remove i}\<close>:\<close>
  mutation_remove_adapted_sending:
    "{\<hole> \<guillemotleft> remove i}
    \<longrightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove i \<triangleleft> \<star>\<^bsup>n\<^esup> X \<guillemotleft> remove (n + i) \<bar> Some (A \<triangleleft> \<star>\<^bsup>n\<^esup> X)\<rparr>
    {\<hole> \<guillemotleft> remove (n + i)}" |
  mutation_remove_adapted_receiving:
    "{\<hole> \<guillemotleft> remove i}
    \<longrightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove i \<triangleright> \<star>\<^bsup>n\<^esup> X \<bar> Some (A \<triangleright> \<star>\<^bsup>Suc n\<^esup> X \<guillemotleft> move n (n + i))\<rparr>
    {\<hole> \<guillemotleft> move (n + i) n}" |
  mutation_remove_adapted_communication:
    "{\<hole> \<guillemotleft> remove i} \<longrightarrow>\<^sub>s\<lparr>\<tau> \<bar> Some \<tau>\<rparr> {\<hole> \<guillemotleft> remove i}" |
  \<comment> \<open>\<^term>\<open>{\<hole> \<guillemotleft> \<E>}\<close> where \<^term>\<open>injective \<E>\<close>:\<close>
  mutation_injectively_adapted_io:
    "{\<hole> \<guillemotleft> \<E>} \<longrightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> \<E>) n (X \<guillemotleft> on_suffix n \<E>) \<bar> Some (IO \<eta> A n X)\<rparr> {\<hole> \<guillemotleft> on_suffix n \<E>}"
    if "injective \<E>" |
  mutation_injectively_adapted_communication:
    "{\<hole> \<guillemotleft> \<E>} \<longrightarrow>\<^sub>s\<lparr>\<tau> \<bar> Some \<tau>\<rparr> {\<hole> \<guillemotleft> \<E>}"
    if "injective \<E>" |
  \<comment> \<open>\<^term>\<open>I OO J\<close>:\<close>
  mutation_composition_none:
    "I OO J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> None\<rparr> I OO J'"
    if "I \<in> \<U>" and "J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> None\<rparr> J'" |
  mutation_composition_some:
    "I OO J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> I' OO J'"
    if "I \<longrightarrow>\<^sub>s\<lparr>\<beta> \<bar> \<omega>\<rparr> I'" and "J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> Some \<beta>\<rparr> J'"

interpretation synchronous:
  mutation_system
    \<open>synchronous_transition\<close>
    \<open>synchronous_transition\<close>
    \<open>synchronous_shortcut_transition\<close>
    \<open>synchronous_shortcut_transition\<close>
    \<open>\<U>\<close>
    \<open>synchronous_mutation_transition_std\<close>
proof (unfold_locales, fold synchronous_shortcut_transition_def)
  fix \<alpha> and \<omega> and I and I'
  assume "I \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> I'"
  then show "I \<in> \<U> \<and> I' \<in> \<U>"
    using move_is_injective and on_suffix_is_injective
    by
      induction
      (blast intro: universe.intros suffix_adapted_mutation_in_universe power_in_universe)+
next
  fix \<alpha>
  have "\<exists>\<omega> I'. I \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> I' \<and> (\<exists> T'. T \<rightarrow>\<^sub>s\<^sup>?\<lparr>\<omega>\<rparr> T' \<and> I' T' S')"
    if "I \<in> \<U>" and "I T S" and "S \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'"
    for I and S and S' and T
  using that proof (induction arbitrary: \<alpha> S S' T)
    case (parallel_mutation_in_universe P \<alpha> S S' Q)
    then have "P \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'"
      by simp
    then show ?case
    proof cases
      case (communication \<eta> \<mu> A n X P' Q')
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> Q'\<close> have "Q \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some (IO \<mu> A n X)\<rparr> Q'"
        by simp
      moreover have "({P' \<parallel> \<hole>} OO {\<star> \<hole>}\<^bsup>n\<^esup>) Q' S'"
        unfolding \<open>S' = \<star>\<^bsup>n\<^esup> (P' \<parallel> Q')\<close>
        by auto
      ultimately show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close>
        using \<open>\<eta> \<noteq> \<mu>\<close> and \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close>
        by (blast intro: mutation_communication)
    next
      case (parallel_left_io \<eta> A n X P')
      have "Q \<rightarrow>\<^sub>s\<^sup>?\<lparr>None\<rparr> Q"
        by simp
      moreover have "({\<hole> \<guillemotleft> suffix n} OO {P' \<parallel> \<hole>}) Q S'"
        unfolding \<open>S' = P' \<parallel> Q \<guillemotleft> suffix n\<close>
        by auto
      ultimately show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close>
        using \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close>
        by (blast intro: mutation_parallel_left_io)
    next
      case (parallel_left_communication P')
      have "Q \<rightarrow>\<^sub>s\<^sup>?\<lparr>None\<rparr> Q"
        by simp
      moreover have "{P' \<parallel> \<hole>} Q S'"
        unfolding \<open>S' = P' \<parallel> Q\<close>
        by simp
      ultimately show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close>
        using \<open>P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'\<close>
        by (blast intro: mutation_parallel_left_communication)
    next
      case (parallel_right_io \<eta> A n X Q')
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q'\<close> have "Q \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some (IO \<eta> A n X)\<rparr> Q'"
        by simp
      moreover have "{P \<guillemotleft> suffix n \<parallel> \<hole>} Q' S'"
        unfolding \<open>S' = P \<guillemotleft> suffix n \<parallel> Q'\<close>
        by simp
      ultimately show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close>
        by (blast intro: mutation_parallel_right_io)
    next
      case (parallel_right_communication Q')
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'\<close> have "Q \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some \<tau>\<rparr> Q'"
        by simp
      moreover have "{P \<parallel> \<hole>} Q' S'"
        unfolding \<open>S' = P \<parallel> Q'\<close>
        by simp
      ultimately show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close>
        by (blast intro: mutation_parallel_right_communication)
    qed
  next
    case (create_channel_mutation_in_universe \<alpha> S S' P)
    then have "\<nu> a. \<Delta> P a \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'"
      by simp
    then show ?case
    proof cases
      case (scope_opening i n X A)
      from \<open>\<nabla> (\<Delta> P) \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move n i\<rparr> S' \<guillemotleft> move n i\<close>
      have "P \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move n i\<rparr> S' \<guillemotleft> move n i"
        by simp
      then have "P \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some (A \<guillemotleft> tail \<triangleleft> \<star>\<^bsup>n\<^esup> X \<guillemotleft> move n i)\<rparr> S' \<guillemotleft> move n i"
        by simp
      moreover have "{\<hole> \<guillemotleft> move i n} (S' \<guillemotleft> move n i) S'"
        by (simp add: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
      ultimately show ?thesis
        unfolding \<open>\<alpha> = A \<triangleleft> \<star>\<^bsup>Suc n\<^esup> X\<close>
        using \<open>i \<le> n\<close> and \<open>dependent_on_chan_at i X\<close>
        by (blast intro: mutation_scope_opening)
    next
      case (new_channel_io \<eta> A n X \<Q>)
      from \<open>\<nabla> (\<Delta> P) \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> \<Q>\<close>
      have "P \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla> \<Q> \<guillemotleft> move n 0"
        by transfer (simp add: comp_def)
      then have "P \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some (IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n))\<rparr> \<nabla> \<Q> \<guillemotleft> move n 0"
        by simp
      moreover have "({\<hole> \<guillemotleft> move 0 n} OO {\<star> \<hole>}) (\<nabla> \<Q> \<guillemotleft> move n 0) S'"
        unfolding \<open>S' = \<nu> a. \<Q> a\<close>
        by (auto simp add: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
      ultimately show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close>
        by (blast intro: mutation_new_channel_io)
    next
      case (new_channel_communication \<Q>)
      from \<open>\<nabla> (\<Delta> P) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<Q>\<close>
      have "P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<Q>"
        by simp
      then have "P \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some \<tau>\<rparr> \<nabla> \<Q>"
        by simp
      moreover have "{\<star> \<hole>} (\<nabla> \<Q>) S'"
        unfolding \<open>S' = \<nu> a. \<Q> a\<close>
        by simp
      ultimately show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close>
        by (blast intro: mutation_new_channel_communication)
    qed
  next
    case (remove_adapted_mutation_in_universe i \<alpha> S S' P)
    then have "P \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'"
      by simp
    show ?case
    proof (cases \<alpha>)
      case (IO \<eta> B n Y)
      then show ?thesis
      proof (cases \<eta>)
        case Sending
        from \<open>P \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'\<close>
        obtain A and X and P'
          where
            "B = A \<guillemotleft> remove i"
          and
            "Y = X \<guillemotleft> on_suffix n (remove i)"
          and
            "S' = P' \<guillemotleft> on_suffix n (remove i)"
          and
            "P \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> P'"
          unfolding \<open>\<alpha> = IO \<eta> B n Y\<close> and \<open>\<eta> = Sending\<close>
          by (erule sending_transition_from_adapted)
        have "Y = X \<guillemotleft> remove (n + i)" and "S' = P' \<guillemotleft> remove (n + i)"
          unfolding \<open>Y = X \<guillemotleft> on_suffix n (remove i)\<close> and \<open>S' = P' \<guillemotleft> on_suffix n (remove i)\<close>
          by (simp_all only: on_suffix_remove)
        from \<open>P \<rightarrow>\<^sub>s\<lparr>A \<triangleleft> \<star>\<^bsup>n\<^esup> X\<rparr> P'\<close> have "P \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some (A \<triangleleft> \<star>\<^bsup>n\<^esup> X)\<rparr> P'"
          by simp
        moreover have "{\<hole> \<guillemotleft> remove (n + i)} P' S'"
          unfolding \<open>S' = P' \<guillemotleft> remove (n + i)\<close>
          by simp
        ultimately show ?thesis
          unfolding
            \<open>\<alpha> = IO \<eta> B n Y\<close>
          and
            \<open>\<eta> = Sending\<close>
          and
            \<open>B = A \<guillemotleft> remove i\<close>
          and
            \<open>Y = X \<guillemotleft> remove (n + i)\<close>
          by (blast intro: mutation_remove_adapted_sending)
      next
        case Receiving
        from \<open>P \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'\<close>
        obtain A
          where
            "B = A \<guillemotleft> remove i"
          and
            "P \<rightarrow>\<^sub>s\<lparr>A \<triangleright> \<star>\<^bsup>Suc n\<^esup> Y \<guillemotleft> move n (n + i)\<rparr> S' \<guillemotleft> move n (n + i)"
          unfolding \<open>\<alpha> = IO \<eta> B n Y\<close> and \<open>\<eta> = Receiving\<close>
          by (metis receiving_transition_from_adapted receiving_transition_with_remove_adapted_source_part)
        from this(2) have "P \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some (A \<triangleright> \<star>\<^bsup>Suc n\<^esup> Y \<guillemotleft> move n (n + i))\<rparr> S' \<guillemotleft> move n (n + i)"
          by simp
        moreover have "{\<hole> \<guillemotleft> move (n + i) n} (S' \<guillemotleft> move n (n + i)) S'"
          by (simp add: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
        ultimately show ?thesis
          unfolding \<open>\<alpha> = IO \<eta> B n Y\<close> and \<open>\<eta> = Receiving\<close> and \<open>B = A \<guillemotleft> remove i\<close>
          by (blast intro: mutation_remove_adapted_receiving)
      qed
    next
      case Communication
      from \<open>P \<guillemotleft> remove i \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'\<close>
      obtain P' where "S' = P' \<guillemotleft> remove i" and "P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'"
        unfolding \<open>\<alpha> = \<tau>\<close>
        by (erule communication_transition_from_adapted)
      from \<open>P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'\<close> have "P \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some \<tau>\<rparr> P'"
        by simp
      moreover have "{\<hole> \<guillemotleft> remove i} P' S'"
        unfolding \<open>S' = P' \<guillemotleft> remove i\<close>
        by simp
      ultimately show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close>
        by (blast intro: mutation_remove_adapted_communication)
    qed
  next
    case (injectively_adapted_mutation_in_universe \<E> \<alpha> S S' P)
    from \<open>injective \<E>\<close> obtain \<D> where "\<D> \<bullet> \<E> = \<one>" and "\<E> \<bullet> \<D> = \<one>"
      by (erule injective_elimination)
    from \<open>{\<hole> \<guillemotleft> \<E>} P S\<close> and \<open>\<E> \<bullet> \<D> = \<one>\<close> have "P = S \<guillemotleft> \<D>"
      by (simp add: composition_adapted [symmetric] identity_adapted)
    show ?case
    proof (cases \<alpha>)
      case (IO \<eta> A n X)
      from \<open>\<D> \<bullet> \<E> = \<one>\<close> have "A = A \<guillemotleft> \<D> \<guillemotleft> \<E>"
        by (simp only: composition_adapted [symmetric] identity_adapted)
      from \<open>\<D> \<bullet> \<E> = \<one>\<close>
      have "X = X \<guillemotleft> on_suffix n \<D> \<guillemotleft> on_suffix n \<E>" and "S' = S' \<guillemotleft> on_suffix n \<D> \<guillemotleft> on_suffix n \<E>"
        by
          (simp_all only:
            composition_adapted [symmetric]
            composition_as_on_suffix
            identity_as_on_suffix [symmetric]
            identity_adapted
          )
      from \<open>S \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'\<close> have "P \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> \<D>) n (X \<guillemotleft> on_suffix n \<D>)\<rparr> S' \<guillemotleft> on_suffix n \<D>"
        unfolding \<open>P = S \<guillemotleft> \<D>\<close> and \<open>\<alpha> = IO \<eta> A n X\<close>
        by (fact adapted_io_transition)
      moreover have "{\<hole> \<guillemotleft> on_suffix n \<E>} (S' \<guillemotleft> on_suffix n \<D>) S'"
        by (simp add: \<open>S' = S' \<guillemotleft> on_suffix n \<D> \<guillemotleft> on_suffix n \<E>\<close> [symmetric])
      ultimately show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close>
        by 
          (
            subst \<open>A = A \<guillemotleft> \<D> \<guillemotleft> \<E>\<close>,
            subst \<open>X = X \<guillemotleft> on_suffix n \<D> \<guillemotleft> on_suffix n \<E>\<close>,
            fastforce intro: mutation_injectively_adapted_io [OF \<open>injective \<E>\<close>]
          )
    next
      case Communication
      from \<open>\<D> \<bullet> \<E> = \<one>\<close> have "S' = S' \<guillemotleft> \<D> \<guillemotleft> \<E>"
        by (simp_all only: composition_adapted [symmetric] identity_adapted)
      from \<open>S \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'\<close> have "P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> S' \<guillemotleft> \<D>"
        unfolding \<open>P = S \<guillemotleft> \<D>\<close> and \<open>\<alpha> = \<tau>\<close>
        by (fact adapted_communication_transition)
      moreover have "{\<hole> \<guillemotleft> \<E>} (S' \<guillemotleft> \<D>) S'"
        by (simp add: \<open>S' = S' \<guillemotleft> \<D> \<guillemotleft> \<E>\<close> [symmetric])
      ultimately show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close>
        by (fastforce intro: mutation_injectively_adapted_communication [OF \<open>injective \<E>\<close>])
    qed
  next
    case (composition_in_universe I J \<alpha> S S' U)
    from \<open>(I OO J) U S\<close> obtain T where "I U T" and "J T S"
      by blast
    from composition_in_universe.IH(2) and \<open>J T S\<close> and \<open>S \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S'\<close>
    obtain \<omega> and J' and T' where "J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> J'" and "T \<rightarrow>\<^sub>s\<^sup>?\<lparr>\<omega>\<rparr> T'" and "J' T' S'"
      by blast
    show ?case
    proof (cases \<omega>)
      case None
      from \<open>I \<in> \<U>\<close> and \<open>J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> J'\<close> have "I OO J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> None\<rparr> I OO J'"
        unfolding \<open>\<omega> = None\<close>
        by (fact mutation_composition_none)
      moreover
      have "U \<rightarrow>\<^sub>s\<^sup>?\<lparr>None\<rparr> U"
        by simp
      moreover
      from \<open>T \<rightarrow>\<^sub>s\<^sup>?\<lparr>\<omega>\<rparr> T'\<close> have "T = T'"
        unfolding \<open>\<omega> = None\<close>
        by simp
      with \<open>I U T\<close> and \<open>J' T' S'\<close> have "(I OO J') U S'"
        by blast
      ultimately show ?thesis
        by blast
    next
      case (Some \<beta>)
      from \<open>T \<rightarrow>\<^sub>s\<^sup>?\<lparr>\<omega>\<rparr> T'\<close> have "T \<rightarrow>\<^sub>s\<lparr>\<beta>\<rparr> T'"
        unfolding \<open>\<omega> = Some \<beta>\<close>
        by simp
      with composition_in_universe.IH(1) and \<open>I U T\<close>
      obtain \<psi> and I' and U' where "I \<longrightarrow>\<^sub>s\<lparr>\<beta> \<bar> \<psi>\<rparr> I'" and "U \<rightarrow>\<^sub>s\<^sup>?\<lparr>\<psi>\<rparr> U'" and "I' U' T'"
        by blast
      from \<open>I \<longrightarrow>\<^sub>s\<lparr>\<beta> \<bar> \<psi>\<rparr> I'\<close> and \<open>J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> J'\<close>
      have "I OO J \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<psi>\<rparr> I' OO J'"
        unfolding \<open>\<omega> = Some \<beta>\<close>
        by (fact mutation_composition_some)
      moreover
      from \<open>I' U' T'\<close> and \<open>J' T' S'\<close> have "(I' OO J') U' S'"
        by blast
      ultimately show ?thesis
        using \<open>U \<rightarrow>\<^sub>s\<^sup>?\<lparr>\<psi>\<rparr> U'\<close>
        by blast
    qed
  qed
  then show "\<forall>I \<in> \<U>. I OO (\<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr>) \<le> \<Squnion> {(\<rightarrow>\<^sub>s\<^sup>?\<lparr>\<omega>\<rparr>) OO I' |\<omega> I'. I \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> I'}"
    by fastforce
next
  fix \<alpha>
  have "\<exists>S'. S \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S' \<and> I' T' S'"
    if "I \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> I'" and "I T S" and "T \<rightarrow>\<^sub>s\<^sup>?\<lparr>\<omega>\<rparr> T'"
    for \<omega> and I and I' and S and T and T'
  using that proof (induction arbitrary: S T T')
    case mutation_communication
    then show ?case
      using communication
      by (simp add: relcompp_apply)
  next
    case mutation_parallel_left_io
    then show ?case
      using parallel_left_io
      by (simp add: relcompp_apply)
  next
    case mutation_parallel_left_communication
    then show ?case
      using parallel_left_communication
      by simp
  next
    case mutation_parallel_right_io
    then show ?case
      using parallel_right_io
      by simp
  next
    case mutation_parallel_right_communication
    then show ?case
      using parallel_right_communication
      by simp
  next
    case mutation_scope_opening
    then show ?case
      using scope_opening
      by (simp add: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
  next
    case (mutation_new_channel_io \<eta> A n X S P P')
    from \<open>P \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some (IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n))\<rparr> P'\<close>
    have "P \<rightarrow>\<^sub>s\<^sup>?\<lparr>Some (IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n))\<rparr> \<nabla>\<^bsub>n\<^esub> (\<Delta> (P' \<guillemotleft> move 0 n))"
      by transfer (simp add: stake_shift sdrop_shift id_stake_snth_sdrop [symmetric, simplified])
    with \<open>{\<star> \<hole>} P S\<close> show ?case
      using new_channel_io
      by (simp add: relcompp_apply)
  next
    case mutation_new_channel_communication
    then show ?case
      using new_channel_communication
      by simp
  next
    case (mutation_remove_adapted_sending i A n X S P P')
    then show ?case
      using adapted_io_transition [where \<E> = "remove i"]
      by (simp add: on_suffix_remove)
  next
    case mutation_remove_adapted_receiving
    then show ?case
      using receiving_transition_with_remove_adapted_source_part
      by (simp add: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
  next
    case mutation_remove_adapted_communication
    then show ?case
      using adapted_communication_transition
      by simp
  next
    case mutation_injectively_adapted_io
    then show ?case
      using adapted_io_transition
      by simp
  next
    case mutation_injectively_adapted_communication
    then show ?case
      using adapted_communication_transition
      by simp
  next
    case mutation_composition_none
    then show ?case
      by fastforce
  next
    case mutation_composition_some
    then show ?case
      by fastforce
  qed
  then show "\<forall>I' \<in> \<U>. \<Squnion> {I\<inverse>\<inverse> OO (\<rightarrow>\<^sub>s\<^sup>?\<lparr>\<omega>\<rparr>) | \<omega> I. I \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> \<omega>\<rparr> I'} \<le> (\<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr>) OO I'\<inverse>\<inverse>"
    by blast
qed

notation synchronous.mutant_lifting (\<open>\<M>\<close>)

interpretation synchronous:
  weak_mutation_system
    \<open>synchronous_transition\<close>
    \<open>synchronous_shortcut_transition\<close>
    \<open>\<U>\<close>
    \<open>synchronous_mutation_transition_std\<close>
    \<open>\<tau>\<close>
proof
  have "\<exists>S'. S \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> S' \<and> I T' S'"
    if "I \<in> \<U>" and "I T S" and "T \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> T'"
    for I and S and T and T'
  using that proof (induction arbitrary: S T T')
    case parallel_mutation_in_universe
    then show ?case
      using parallel_right_communication
      by simp
  next
    case create_channel_mutation_in_universe
    then show ?case
      using new_channel_communication
      by simp
  next
    case remove_adapted_mutation_in_universe
    then show ?case
      using adapted_communication_transition
      by simp
  next
    case injectively_adapted_mutation_in_universe
    then show ?case
      using adapted_communication_transition
      by simp
  next
    case composition_in_universe
    then show ?case
      by blast
  qed
  then show "\<forall>I \<in> \<U>. I\<inverse>\<inverse> OO (\<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>) \<le> (\<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr>) OO I\<inverse>\<inverse>"
    by blast
next
  fix \<alpha> and I and I'
  assume "I \<longrightarrow>\<^sub>s\<lparr>\<alpha> \<bar> Some \<tau>\<rparr> I'"
  then have "\<alpha> = \<tau>" and "I = I'"
    by (induction I \<alpha> "Some \<tau>" I') auto
  then show "I\<inverse>\<inverse> \<le> (\<Rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr>) OO I'\<inverse>\<inverse>"
    by fastforce
qed

(*FIXME:
  Use a locale to prove the (quasi-)compatibility lemmas only once for \<^theory_text>\<open>synchronous\<close> and
  \<^theory_text>\<open>synchronous.weak\<close> and then also for \<^theory_text>\<open>synchronous.mixed\<close>. Do only the setup for the solvers
  explicitly for both \<^theory_text>\<open>synchronous\<close> and \<^theory_text>\<open>synchronous.weak\<close>.
*)

lemma receive_is_quasi_compatible_with_synchronous_bisimilarity:
  assumes "\<And>n X. (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e) \<sim>\<^sub>s (\<lambda>e. (\<Q> (X e) \<guillemotleft> suffix n) e)"
  shows "A \<triangleright> x. \<P> x \<sim>\<^sub>s A \<triangleright> x. \<Q> x"
using assms
proof (coinduction arbitrary: \<P> \<Q> rule: synchronous.symmetric_up_to_rule [where \<F> = "[\<sim>\<^sub>s]"])
  case symmetry
  then show ?case
    by (blast intro: synchronous.bisimilarity_symmetry_rule)
next
  case simulation
  from simulation(2,1) show ?case
    by cases (auto simp del: receive_def intro: synchronous_transition.receiving)
qed respectful

text \<open>
  We prove commutativity of parallel composition already here, since we need it to prove
  compatibility of parallel composition for both bisimilarity and weak bisimilarity.
\<close>

lemma parallel_commutativity:
  shows "P \<parallel> Q \<sim>\<^sub>s Q \<parallel> P"
proof (coinduction arbitrary: P Q rule: synchronous.symmetric_up_to_rule [where \<F> = \<M>])
  case (simulation \<alpha> S P Q)
  then show ?case
  proof cases
    case (communication \<eta> \<mu> A n X P' Q')
    from \<open>\<eta> \<noteq> \<mu>\<close> and \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> Q'\<close> and \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close>
    have "Q \<parallel> P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (Q' \<parallel> P')"
      by (intro synchronous_transition.communication) simp_all
    then show ?thesis
      unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<star>\<^bsup>n\<^esup> (P' \<parallel> Q')\<close>
      using power_in_universe [OF create_channel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_left_io \<eta> A n X P')
    from \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close> have "Q \<parallel> P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q \<guillemotleft> suffix n \<parallel> P'"
      by (fact synchronous_transition.parallel_right_io)
    then show ?thesis
      unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = P' \<parallel> Q \<guillemotleft> suffix n\<close>
      using equality_in_universe
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_left_communication P')
    from \<open>P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'\<close> have "Q \<parallel> P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q \<parallel> P'"
      by (fact synchronous_transition.parallel_right_communication)
    then show ?thesis
      unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = P' \<parallel> Q\<close>
      using equality_in_universe
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> A n X Q')
    from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q'\<close> have "Q \<parallel> P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q' \<parallel> P \<guillemotleft> suffix n"
      by (fact synchronous_transition.parallel_left_io)
    then show ?thesis
      unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = P \<guillemotleft> suffix n \<parallel> Q'\<close>
      using equality_in_universe
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_communication Q')
    from \<open>Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'\<close> have "Q \<parallel> P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q' \<parallel> P"
      by (fact synchronous_transition.parallel_left_communication)
    then show ?thesis
      unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = P \<parallel> Q'\<close>
      using equality_in_universe
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  qed
qed (respectful, blast)

lemma parallel_is_right_compatible_with_synchronous_bisimilarity:
  assumes "Q\<^sub>1 \<sim>\<^sub>s Q\<^sub>2"
  shows "P \<parallel> Q\<^sub>1 \<sim>\<^sub>s P \<parallel> Q\<^sub>2"
  using
    synchronous.mutation_is_compatible_with_bisimilarity [OF parallel_mutation_in_universe]
  and
    assms
  by simp

lemma parallel_is_left_compatible_with_synchronous_bisimilarity:
  assumes "P\<^sub>1 \<sim>\<^sub>s P\<^sub>2"
  shows "P\<^sub>1 \<parallel> Q \<sim>\<^sub>s P\<^sub>2 \<parallel> Q"
  using
    parallel_is_right_compatible_with_synchronous_bisimilarity and parallel_commutativity
  and
    assms
  by (meson synchronous.bisimilarity_transitivity_rule)

lemma parallel_is_compatible_with_synchronous_bisimilarity:
  assumes "P\<^sub>1 \<sim>\<^sub>s P\<^sub>2" and "Q\<^sub>1 \<sim>\<^sub>s Q\<^sub>2"
  shows "P\<^sub>1 \<parallel> Q\<^sub>1 \<sim>\<^sub>s P\<^sub>2 \<parallel> Q\<^sub>2"
  using
    parallel_is_right_compatible_with_synchronous_bisimilarity
  and
    parallel_is_left_compatible_with_synchronous_bisimilarity
  and
    assms
  by (meson synchronous.bisimilarity_transitivity_rule)

lemma general_parallel_is_compatible_with_synchronous_bisimilarity:
  assumes "\<And>v. \<P>\<^sub>1 v \<sim>\<^sub>s \<P>\<^sub>2 v"
  shows "\<Prod>v \<leftarrow> vs. \<P>\<^sub>1 v \<sim>\<^sub>s \<Prod>v \<leftarrow> vs. \<P>\<^sub>2 v"
  using parallel_is_compatible_with_synchronous_bisimilarity and assms
  by (induction vs) simp_all

lemma create_channel_is_compatible_with_synchronous_bisimilarity:
  assumes "P\<^sub>1 \<sim>\<^sub>s P\<^sub>2"
  shows "\<star> P\<^sub>1 \<sim>\<^sub>s \<star> P\<^sub>2"
  using
    synchronous.mutation_is_compatible_with_bisimilarity [OF create_channel_mutation_in_universe]
  and
    assms
  by simp

lemma tagged_create_channel_is_compatible_with_synchronous_bisimilarity:
  assumes "P\<^sub>1 \<sim>\<^sub>s P\<^sub>2"
  shows "\<langle>t\<rangle> \<star> P\<^sub>1 \<sim>\<^sub>s \<langle>t\<rangle> \<star> P\<^sub>2"
  using create_channel_is_compatible_with_synchronous_bisimilarity and assms
  by simp

lemma create_channel_power_is_compatible_with_synchronous_bisimilarity:
  assumes "P\<^sub>1 \<sim>\<^sub>s P\<^sub>2"
  shows "\<star>\<^bsup>n\<^esup> P\<^sub>1 \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> P\<^sub>2"
  using
    synchronous.mutation_is_compatible_with_bisimilarity
      [OF power_in_universe [OF create_channel_mutation_in_universe]]
  and
    assms
  by simp

lemma wrapped_remove_adapted_is_compatible_with_synchronous_bisimilarity:
  assumes "P\<^sub>1 \<sim>\<^sub>s P\<^sub>2"
  shows "wrapped_remove_adapted P\<^sub>1 i \<sim>\<^sub>s wrapped_remove_adapted P\<^sub>2 i"
  using
    synchronous.mutation_is_compatible_with_bisimilarity [OF remove_adapted_mutation_in_universe]
  and
    assms
  by simp

quotient_type synchronous_behavior = "process family" / "(\<sim>\<^sub>s)"
  using synchronous.bisimilarity_is_equivalence .

declare synchronous_behavior.abs_eq_iff [equivalence_transfer]

lift_definition
  synchronous_behavior_stop :: synchronous_behavior
  is stop .

declare synchronous_behavior_stop.abs_eq [equivalence_transfer]

lift_definition
  synchronous_behavior_send :: "chan family \<Rightarrow> val family \<Rightarrow> synchronous_behavior"
  is send .

declare synchronous_behavior_send.abs_eq [equivalence_transfer]

lift_definition
  synchronous_behavior_receive :: "chan family \<Rightarrow> (val \<Rightarrow> process family) \<Rightarrow> synchronous_behavior"
  is receive .

declare synchronous_behavior_receive.abs_eq [equivalence_transfer]

lift_definition
  synchronous_behavior_parallel :: "
    synchronous_behavior \<Rightarrow>
    synchronous_behavior \<Rightarrow>
    synchronous_behavior"
  is parallel
  using parallel_is_compatible_with_synchronous_bisimilarity .

declare synchronous_behavior_parallel.abs_eq [equivalence_transfer]

lift_definition
  synchronous_behavior_general_parallel :: "
    ('a \<Rightarrow> synchronous_behavior) \<Rightarrow>
    'a list \<Rightarrow>
    synchronous_behavior"
  is general_parallel
  using general_parallel_is_compatible_with_synchronous_bisimilarity .

declare synchronous_behavior_general_parallel.abs_eq [equivalence_transfer]

lift_definition
  synchronous_behavior_create_channel :: "synchronous_behavior \<Rightarrow> synchronous_behavior"
  is create_channel
  using create_channel_is_compatible_with_synchronous_bisimilarity .

declare synchronous_behavior_create_channel.abs_eq [equivalence_transfer]

lift_definition
  synchronous_behavior_tagged_create_channel :: "nat \<Rightarrow> synchronous_behavior \<Rightarrow> synchronous_behavior"
  is tagged_create_channel
  using tagged_create_channel_is_compatible_with_synchronous_bisimilarity .

declare synchronous_behavior_tagged_create_channel.abs_eq [equivalence_transfer]

lift_definition
  synchronous_behavior_wrapped_remove_adapted :: "synchronous_behavior \<Rightarrow> nat \<Rightarrow> synchronous_behavior"
  is wrapped_remove_adapted
  using wrapped_remove_adapted_is_compatible_with_synchronous_bisimilarity .

declare synchronous_behavior_wrapped_remove_adapted.abs_eq [equivalence_transfer]

text \<open>
  Now for weak bisimilarity.
\<close>

(*FIXME:
  Make the following changes above and below:

    \<^item> Add compatibility lemmas for \<open>\<guillemotleft> remove _\<close> and \<open>\<guillemotleft> move\<close>

    \<^item> Remove the compatibility lemmas for \<open>wrapped_remove_adapted\<close> and instead use the compatibility
      lemmas for \<open>\<guillemotleft> remove _\<close> and unfolding with \<open>wrapped_remove_adapted\<close> directly in the
      \<^theory_text>\<open>lift_definition\<close> proofs
*)

lemma receive_is_quasi_compatible_with_synchronous_weak_bisimilarity:
  assumes "\<And>n X. (\<lambda>e. (\<P> (X e) \<guillemotleft> suffix n) e) \<approx>\<^sub>s (\<lambda>e. (\<Q> (X e) \<guillemotleft> suffix n) e)"
  shows "A \<triangleright> x. \<P> x \<approx>\<^sub>s A \<triangleright> x. \<Q> x"
using assms unfolding synchronous.weak_bisimilarity_is_mixed_bisimilarity
proof (coinduction arbitrary: \<P> \<Q> rule: synchronous.mixed.symmetric_up_to_rule [where \<F> = "[\<asymp>\<^sub>s]"])
  case symmetry
  then show ?case
    by (blast intro: synchronous.mixed.bisimilarity_symmetry_rule)
next
  case simulation
  from simulation(2,1) show ?case
    by cases (auto simp del: receive_def intro: synchronous_transition.receiving)
qed respectful

lemma parallel_is_right_compatible_with_synchronous_weak_bisimilarity:
  assumes "Q\<^sub>1 \<approx>\<^sub>s Q\<^sub>2"
  shows "P \<parallel> Q\<^sub>1 \<approx>\<^sub>s P \<parallel> Q\<^sub>2"
  using
    synchronous.mixed.mutation_is_compatible_with_bisimilarity [OF parallel_mutation_in_universe]
  and
    assms
  unfolding synchronous.weak_bisimilarity_is_mixed_bisimilarity
  by simp

lemma parallel_is_left_compatible_with_synchronous_weak_bisimilarity:
  assumes "P\<^sub>1 \<approx>\<^sub>s P\<^sub>2"
  shows "P\<^sub>1 \<parallel> Q \<approx>\<^sub>s P\<^sub>2 \<parallel> Q"
  using
    parallel_is_right_compatible_with_synchronous_weak_bisimilarity and parallel_commutativity
  and
    assms
  by
    (meson
      synchronous.bisimilarity_in_weak_bisimilarity [THEN predicate2D]
      synchronous.weak.bisimilarity_transitivity_rule
    )

lemma parallel_is_compatible_with_synchronous_weak_bisimilarity:
  assumes "P\<^sub>1 \<approx>\<^sub>s P\<^sub>2" and "Q\<^sub>1 \<approx>\<^sub>s Q\<^sub>2"
  shows "P\<^sub>1 \<parallel> Q\<^sub>1 \<approx>\<^sub>s P\<^sub>2 \<parallel> Q\<^sub>2"
  using
    parallel_is_right_compatible_with_synchronous_weak_bisimilarity
  and
    parallel_is_left_compatible_with_synchronous_weak_bisimilarity
  and
    assms
  by (meson synchronous.weak.bisimilarity_transitivity_rule)

lemma general_parallel_is_compatible_with_synchronous_weak_bisimilarity:
  assumes "\<And>v. \<P>\<^sub>1 v \<approx>\<^sub>s \<P>\<^sub>2 v"
  shows "\<Prod>v \<leftarrow> vs. \<P>\<^sub>1 v \<approx>\<^sub>s \<Prod>v \<leftarrow> vs. \<P>\<^sub>2 v"
  using parallel_is_compatible_with_synchronous_weak_bisimilarity and assms
  by (induction vs) simp_all

lemma create_channel_is_compatible_with_synchronous_weak_bisimilarity:
  assumes "P\<^sub>1 \<approx>\<^sub>s P\<^sub>2"
  shows "\<star> P\<^sub>1 \<approx>\<^sub>s \<star> P\<^sub>2"
  using
    synchronous.mixed.mutation_is_compatible_with_bisimilarity
      [OF create_channel_mutation_in_universe]
  and
    assms
  unfolding synchronous.weak_bisimilarity_is_mixed_bisimilarity
  by simp

lemma tagged_create_channel_is_compatible_with_synchronous_weak_bisimilarity:
  assumes "P\<^sub>1 \<approx>\<^sub>s P\<^sub>2"
  shows "\<langle>t\<rangle> \<star> P\<^sub>1 \<approx>\<^sub>s \<langle>t\<rangle> \<star> P\<^sub>2"
  using create_channel_is_compatible_with_synchronous_weak_bisimilarity and assms
  by simp

lemma create_channel_power_is_compatible_with_synchronous_weak_bisimilarity:
  assumes "P\<^sub>1 \<approx>\<^sub>s P\<^sub>2"
  shows "\<star>\<^bsup>n\<^esup> P\<^sub>1 \<approx>\<^sub>s \<star>\<^bsup>n\<^esup> P\<^sub>2"
  using
    synchronous.mixed.mutation_is_compatible_with_bisimilarity
      [OF power_in_universe [OF create_channel_mutation_in_universe]]
  and
    assms
  unfolding synchronous.weak_bisimilarity_is_mixed_bisimilarity
  by simp

lemma wrapped_remove_adapted_is_compatible_with_synchronous_weak_bisimilarity:
  assumes "P\<^sub>1 \<approx>\<^sub>s P\<^sub>2"
  shows "wrapped_remove_adapted P\<^sub>1 i \<approx>\<^sub>s wrapped_remove_adapted P\<^sub>2 i"
  using
    synchronous.mixed.mutation_is_compatible_with_bisimilarity
      [OF remove_adapted_mutation_in_universe]
  and
    assms
  unfolding synchronous.weak_bisimilarity_is_mixed_bisimilarity
  by simp

quotient_type synchronous_weak_behavior = "process family" / "(\<approx>\<^sub>s)"
  using synchronous.weak.bisimilarity_is_equivalence .

declare synchronous_weak_behavior.abs_eq_iff [equivalence_transfer]

lift_definition
  synchronous_weak_behavior_stop :: synchronous_weak_behavior
  is stop .

declare synchronous_weak_behavior_stop.abs_eq [equivalence_transfer]

lift_definition
  synchronous_weak_behavior_send :: "chan family \<Rightarrow> val family \<Rightarrow> synchronous_weak_behavior"
  is send .

declare synchronous_weak_behavior_send.abs_eq [equivalence_transfer]

lift_definition
  synchronous_weak_behavior_receive :: "chan family \<Rightarrow> (val \<Rightarrow> process family) \<Rightarrow> synchronous_weak_behavior"
  is receive .

declare synchronous_weak_behavior_receive.abs_eq [equivalence_transfer]

lift_definition
  synchronous_weak_behavior_parallel :: "
    synchronous_weak_behavior \<Rightarrow>
    synchronous_weak_behavior \<Rightarrow>
    synchronous_weak_behavior"
  is parallel
  using parallel_is_compatible_with_synchronous_weak_bisimilarity .

declare synchronous_weak_behavior_parallel.abs_eq [equivalence_transfer]

lift_definition
  synchronous_weak_behavior_general_parallel :: "
    ('a \<Rightarrow> synchronous_weak_behavior) \<Rightarrow>
    'a list \<Rightarrow>
    synchronous_weak_behavior"
  is general_parallel
  using general_parallel_is_compatible_with_synchronous_weak_bisimilarity .

declare synchronous_weak_behavior_general_parallel.abs_eq [equivalence_transfer]

lift_definition
  synchronous_weak_behavior_create_channel :: "synchronous_weak_behavior \<Rightarrow> synchronous_weak_behavior"
  is create_channel
  using create_channel_is_compatible_with_synchronous_weak_bisimilarity .

declare synchronous_weak_behavior_create_channel.abs_eq [equivalence_transfer]

lift_definition
  synchronous_weak_behavior_tagged_create_channel :: "nat \<Rightarrow> synchronous_weak_behavior \<Rightarrow> synchronous_weak_behavior"
  is tagged_create_channel
  using tagged_create_channel_is_compatible_with_synchronous_weak_bisimilarity .

declare synchronous_weak_behavior_tagged_create_channel.abs_eq [equivalence_transfer]

lift_definition
  synchronous_weak_behavior_wrapped_remove_adapted :: "synchronous_weak_behavior \<Rightarrow> nat \<Rightarrow> synchronous_weak_behavior"
  is wrapped_remove_adapted
  using wrapped_remove_adapted_is_compatible_with_synchronous_weak_bisimilarity .

declare synchronous_behavior_wrapped_remove_adapted.abs_eq [equivalence_transfer]

text \<open>
  Setup of automatic conversion from bisimilarities into weak bisimilarities.
\<close>

declare synchronous.bisimilarity_in_weak_bisimilarity [equivalence]

end
