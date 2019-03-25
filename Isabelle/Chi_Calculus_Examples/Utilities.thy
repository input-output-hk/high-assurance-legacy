section \<open>Utilities\<close>

theory Utilities
  imports
    Chi_Calculus.Processes
    Chi_Calculus.Proper_Weak_Bisimulation
    "HOL-Library.BNF_Corec"
begin

lemma proper_transitions_from_receive:
  assumes "a \<triangleright> x. P x \<rightarrow>\<^sub>\<sharp> c"
  obtains x where "c = \<lparr>a \<triangleright> x\<rparr> P x"
  using assms
proof (induction "a \<triangleright> x. P x" c)
  case simple
  then show ?case
  proof cases
    case receiving
    then show ?thesis
      (* TODO: Find a nicer proof. *)
      by (metis basic_action.distinct(1) basic_action.inject basic_action_of.simps(1) basic_action_of.simps(2) io_action.inject(2) proper_action.exhaust simple.prems)
  next
    case scoped_acting
    then show ?thesis
      using no_opening_transitions_from_receive by simp
  qed
next
  case output_without_opening
  then show ?case
    using basic_transitions_from_receive by auto
next
  case output_with_opening
  then show ?case
    using no_opening_transitions_from_receive by blast
qed

context begin

private definition
  p0 :: "val \<Rightarrow> (val \<Rightarrow> process) \<Rightarrow> process"
where
  "p0 y P \<equiv> \<nu> c. (c \<triangleleft> y \<parallel> c \<triangleright> x. P x)"

private definition
  p1 :: "val \<Rightarrow> (val \<Rightarrow> process) \<Rightarrow> process"
where
  "p1 y P \<equiv> P y"

private inductive
  bisim_rel :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  p0_p1: "bisim_rel (p0 y P) (p1 y P)" |
  p1_p0: "bisim_rel (p1 y P) (p0 y P)" |
  id:    "bisim_rel p p"

(* TODO: Prove it. *)
private lemma transitions_from_p0: "(\<exists>!d. p0 y P \<rightarrow>\<^sub>\<sharp> d) \<and> (THE d. p0 y P \<rightarrow>\<^sub>\<sharp> d) = \<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)" sorry
(* private lemma transitions_from_p0: "\<exists>d. p0 y P \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> d \<and> (\<forall>d. p0 y P \<rightarrow>\<^sub>\<sharp> d \<longrightarrow> d = \<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y))" sorry *)

private lemma aux1: "\<nu> c. (\<zero> \<parallel> p) \<sim>\<^sub>\<sharp> p"
proof -
  have "\<zero> \<parallel> p \<sim>\<^sub>\<sharp> p"
    using proper_parallel_unit by simp
  then have "\<nu> c. (\<zero> \<parallel> p) \<sim>\<^sub>\<sharp> \<nu> c. p"
    using proper_new_channel_preservation by simp
  then show ?thesis
    using proper_scope_redundancy and proper.bisimilarity_transitivity_rule by blast
qed

private lemma aux2: "p0 y P \<Rightarrow>\<^sup>\<tau> \<nu> c. (\<zero> \<parallel> P y)"
proof -
  have "p0 y P \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)"
    using transitions_from_p0 and theI2 by metis
  then show ?thesis
    using proper_tau_trans_is_basic_tau_trans and tau_transition_is_tau_sequence by simp_all
qed

private lemma aux3:
  assumes "reflp \<S>"
      and "\<R> = (\<sim>\<^sub>\<sharp>) OO \<S> OO (\<sim>\<^sub>\<sharp>)"
    shows "\<R> (\<nu> c. (\<zero> \<parallel> p)) p"
      and "\<R> p (\<nu> c. (\<zero> \<parallel> p))"
proof -
  have "\<R> (\<nu> c. (\<zero> \<parallel> p)) p"
  proof -
    have "\<nu> c. (\<zero> \<parallel> p) \<sim>\<^sub>\<sharp> p"
      using aux1 by fastforce
    then show ?thesis
      using reflp_ge_eq and assms by blast
  qed
  moreover have "\<R> p (\<nu> c. (\<zero> \<parallel> p))"
  proof -
    have "\<nu> c. (\<zero> \<parallel> p) \<sim>\<^sub>\<sharp> p"
      using aux1 by fastforce
    then have "p \<sim>\<^sub>\<sharp> \<nu> c. (\<zero> \<parallel> p)"
      using proper.bisimilarity_symmetry by simp
    then show ?thesis
      using reflp_ge_eq and assms by blast
  qed
  ultimately show "\<R> (\<nu> c. (\<zero> \<parallel> p)) p" and "\<R> p (\<nu> c. (\<zero> \<parallel> p))"
    by simp_all
qed

lemma internal_communication2: "\<nu> a. (a \<triangleleft> y \<parallel> a \<triangleright> x. P x a) \<approx>\<^sub>\<sharp> \<nu> a. P y a" sorry
lemma "\<nu> a. (a \<triangleleft> y \<parallel> a \<triangleright> x. a \<triangleleft> x) \<approx>\<^sub>\<sharp> \<nu> a. a \<triangleleft> y" using internal_communication2 sorry


(* TODO: Fill holes. *)
lemma internal_communication: "\<nu> c. (c \<triangleleft> y \<parallel> c \<triangleright> x. P x) \<approx>\<^sub>\<sharp> P y"
proof -
  let ?\<R> = "(\<sim>\<^sub>\<sharp>) OO bisim_rel OO (\<sim>\<^sub>\<sharp>)"
  have "bisim_rel (\<nu> c. (c \<triangleleft> y \<parallel> c \<triangleright> x. P x)) (P y)"
    using bisim_rel.p0_p1 and p0_def and p1_def by simp
  then show ?thesis
  proof (coinduct rule: weak_proper_bisim_up_to_strong_bisim)
    case (sim p q)
    then show ?case
    proof cases
      case (p0_p1 y P)
      then show ?thesis
      proof (intro impI allI)
        fix d
        assume "p \<rightarrow>\<^sub>\<sharp> d"
        then show "\<exists>e. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ e \<and> rel_proper_residual ?\<R> d e"
        proof -
          have "d = \<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)"
            using \<open>p \<rightarrow>\<^sub>\<sharp> d\<close> and \<open>p = p0 y P\<close> and transitions_from_p0 by (metis theI_unique)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> q"
            using weak_proper_transition_refl_intro by simp
          moreover have "?\<R> (\<nu> c. (\<zero> \<parallel> P y)) q"
            using aux3 and bisim_rel.id and \<open>q = p1 y P\<close> and p1_def by (simp add: reflpI)
          then have "rel_proper_residual ?\<R> d (\<lparr>\<tau>\<rparr> q)"
            using proper_residual.rel_intros(1) and \<open>d = \<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)\<close> by simp
          ultimately show ?thesis
            by fastforce
        qed
      qed
    next
      case (p1_p0 y P)
      then show ?thesis
      proof (intro impI allI)
        fix d
        assume "p \<rightarrow>\<^sub>\<sharp> d"
        then show "\<exists>e. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ e \<and> rel_proper_residual ?\<R> d e"
        proof cases
          case (simple \<delta> p')
          then show ?thesis
          proof -
            have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> \<nu> c. (\<zero> \<parallel> p')"
            proof -
              have "q \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)"
                using transitions_from_p0 and \<open>q = p0 y P\<close> by (metis theI2)
              moreover have "\<nu> c. (\<zero> \<parallel> P y) \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> \<nu> c. (\<zero> \<parallel> p')"
              proof -
                have "\<zero> \<parallel> P y \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<zero> \<parallel> p'"
                  using \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> p'\<close> and \<open>p = p1 y P\<close> and p1_def and acting_right by simp
                then have "\<nu> c. (\<zero> \<parallel> P y) \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> c. (\<zero> \<parallel> p')"
                  using acting_scope by simp
                then have "\<nu> c. (\<zero> \<parallel> P y) \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> \<nu> c. (\<zero> \<parallel> p')"
                  using proper_transition.simple by simp
                then show ?thesis
                  using weak_tau_respecting_proper_transition_single_simple by simp
              qed
              ultimately show ?thesis
                using prepend_tau_transition_to_weak_proper_transition and weak_proper_transition_def by simp
            qed
            moreover have "rel_proper_residual ?\<R> (\<lparr>\<delta>\<rparr> p') (\<lparr>\<delta>\<rparr> \<nu> c. (\<zero> \<parallel> p'))"
            proof -
              have "?\<R> p' (\<nu> c. (\<zero> \<parallel> p'))"
                using aux3 and bisim_rel.id by (simp add: reflpI)
              then show ?thesis
                using proper_residual.rel_intros(1) by simp
            qed
            ultimately show ?thesis
              using \<open>d = \<lparr>\<delta>\<rparr> p'\<close> by blast
          qed
        next
          case (output_without_opening a x p')
          then show ?thesis
          proof -
            have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleleft> x\<rparr> \<nu> c. (\<zero> \<parallel> p')"
            proof -
              have "q \<Rightarrow>\<^sup>\<tau> \<nu> c. (\<zero> \<parallel> P y)"
                using aux2 and \<open>q = p0 y P\<close> by simp
              moreover have "\<nu> c. (\<zero> \<parallel> P y) \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<nu> c. (\<zero> \<parallel> p')"
              proof -
                have "\<zero> \<parallel> P y \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<zero> \<parallel> p'"
                  using \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> p'\<close> and \<open>p = p1 y P\<close> and p1_def and acting_right by simp
                then have "\<nu> c. (\<zero> \<parallel> P y) \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<nu> c. (\<zero> \<parallel> p')"
                  using acting_scope by simp
                then have "\<nu> c. (\<zero> \<parallel> P y) \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<nu> c. (\<zero> \<parallel> p')"
                  using proper_transition.output_without_opening by simp
                then show ?thesis
                  using weak_tau_respecting_proper_transition_single_output_without_opening by simp
              qed
              ultimately show ?thesis
                using prepend_tau_sequence_to_weak_tau_respecting_proper_transition_output_without_opening and weak_proper_transition_def by simp
            qed
            moreover have "rel_proper_residual ?\<R> (\<lparr>a \<triangleleft> x\<rparr> p') (\<lparr>a \<triangleleft> x\<rparr> \<nu> c. (\<zero> \<parallel> p'))"
            proof -
              have "?\<R> p' (\<nu> c. (\<zero> \<parallel> p'))"
                using aux3 and bisim_rel.id by (simp add: reflpI)
              then have "rel_output_rest ?\<R> (x\<rparr> p') (x\<rparr> \<nu> c. (\<zero> \<parallel> p'))"
                using output_rest.rel_intros(1) by simp
              then show ?thesis
                using proper_residual.rel_intros(2) by simp
            qed
            ultimately show ?thesis
              using \<open>d = \<lparr>a \<triangleleft> x\<rparr> p'\<close> by blast
          qed
        next
          case (output_with_opening P' a K)
          then show ?thesis sorry
        qed
      qed
    next
      case id
      then show ?thesis
        by (smt bisim_rel.id proper.bisimilarity_reflexivity reflpD relcompp_apply weak_proper_sim_reflexivity)
    qed
  next
    case (sym r s)
    then show ?case
      using bisim_rel.simps by blast
  qed
qed

end

lemma weak_proper_parallel_scope_redundancy: "\<nu> c. (p \<parallel> P c) \<approx>\<^sub>\<sharp> p \<parallel> \<nu> c. P c"
  (* FIXME: Find a nicer proof. *)
  by (smt
      weak_proper_scope_redundancy
      weak_proper_bisim_elim2
      weak_proper_bisim_transitivity
      weak_proper_new_channel_preservation
      weak_proper_parallel_commutativity
      weak_proper_parallel_scope_extension)

lemma weak_proper_parallel_scope_extension2: "q \<parallel> \<nu> a. P a \<approx>\<^sub>\<sharp> \<nu> a. (q \<parallel> P a)"
proof -
  have "q \<parallel> \<nu> a. P a \<approx>\<^sub>\<sharp> \<nu> a. P a \<parallel> q"
    using weak_proper_parallel_commutativity by simp
  also have "... \<approx>\<^sub>\<sharp> \<nu> a. (P a \<parallel> q)"
    using weak_proper_parallel_scope_extension by simp
  also have "... \<approx>\<^sub>\<sharp> \<nu> a. (q \<parallel> P a)"
  proof -
    have "\<And>a. P a \<parallel> q \<approx>\<^sub>\<sharp> q \<parallel> P a"
      using weak_proper_parallel_commutativity by simp
    then have "\<nu> a. (P a \<parallel> q) \<approx>\<^sub>\<sharp> \<nu> a. (q \<parallel> P a)"
      using weak_proper_new_channel_preservation by simp
    then show ?thesis
      using weak_proper_bisim_transitivity by simp
  qed
  finally show ?thesis .
qed

(* Generalized parallel composition over finite sets. *)
(* NOTE: The existing \<open>comm_monoid\<close> does not work because \<open>(=)\<close> is used, whereas \<open>(process, \<parallel>, \<zero>)\<close> is
   a commutative monoid when \<open>(\<sim>\<^sub>\<sharp>)\<close> or \<open>(\<approx>\<^sub>\<sharp>)\<close> is used. *)

definition
  big_parallel :: "['a \<Rightarrow> process, 'a list] \<Rightarrow> process"
where
  "big_parallel f xs \<equiv> foldr (\<lambda>x p. f x \<parallel> p) xs \<zero>"

lemma big_parallel_cong [fundef_cong]:
  assumes "xs = ys"
  and "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows "big_parallel f xs = big_parallel g ys"
  using assms
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case
    by (unfold big_parallel_def) simp
next
  case (Cons y ys)
  have "big_parallel f xs = big_parallel f (y # ys)"
    by (simp add: \<open>xs = y # ys\<close>)
  also have "... = f y \<parallel> big_parallel f ys"
    by (simp add: big_parallel_def)
  also have "... = g y \<parallel> big_parallel g ys"
    by (simp add: Cons.IH Cons.prems(1-2))
  also have "... = big_parallel g (y # ys)"
    by (simp add: big_parallel_def)
  finally show ?case
    by simp
qed

abbreviation
  Big_Parallel ("\<parallel>_" [1000] 999)
where
  "\<parallel>ps \<equiv> big_parallel id ps"

syntax (ASCII)
  "_big_parallel" :: "[pttrn, 'a list,  process] \<Rightarrow> process" ("(4PARALLEL (_/:_)./ _)" [0, 51, 10] 10)
syntax
  "_big_parallel" :: "[pttrn, 'a list,  process] \<Rightarrow> process" ("(2\<parallel>(_/\<leftarrow>_)./ _)" [0, 51, 10] 10)
translations
  "\<parallel>x\<leftarrow>xs. p" \<rightleftharpoons> "CONST big_parallel (\<lambda>x. p) xs"

lemma weak_proper_big_parallel_preservation: "(\<And>x. x \<in> set xs \<Longrightarrow> P x \<approx>\<^sub>\<sharp> Q x) \<Longrightarrow> (\<parallel>x\<leftarrow>xs. P x) \<approx>\<^sub>\<sharp> (\<parallel>x\<leftarrow>xs. Q x)"
proof (induction xs)
  case Nil
  have "big_parallel P [] = \<zero>"
    by (simp add: big_parallel_def)
  also have "... = big_parallel Q []"
    by (simp add: big_parallel_def)
  finally show ?case
    by (simp add: weak_proper_bisim_reflexivity)
next
  case (Cons x xs)
  then have "big_parallel P xs \<approx>\<^sub>\<sharp> big_parallel Q xs"
    by simp
  then have "P x \<parallel> big_parallel P xs \<approx>\<^sub>\<sharp> P x \<parallel> big_parallel Q xs"
    using weak_proper_parallel_preservation by simp
  also have "... \<approx>\<^sub>\<sharp> Q x \<parallel> big_parallel Q xs"
    using Cons.prems and weak_proper_parallel_preservation by simp
  finally show ?case
    by (simp add: big_parallel_def)
qed

lemma weak_proper_indexed_big_parallel_preservation:
  "\<lbrakk> n > 0; \<And>i. i\<in>{0..<n} \<Longrightarrow> P i \<approx>\<^sub>\<sharp> Q i \<rbrakk> \<Longrightarrow> (\<parallel>i\<leftarrow>[0..<n]. P i) \<approx>\<^sub>\<sharp> (\<parallel>i\<leftarrow>[0..<n]. Q i)"
  by (metis set_upt weak_proper_big_parallel_preservation)

(* The function \<open>restrict n P\<close> returns the process \<open>\<nu> a\<^sub>1 ... a\<^sub>n. P [a\<^sub>1, ..., a\<^sub>n]\<close>. *)

fun
  restrict  :: "[nat, chan list \<Rightarrow> process] \<Rightarrow> process"
and
  restrict' :: "[nat, chan list, chan list \<Rightarrow> process] \<Rightarrow> process"
where
  "restrict  n          P =  restrict' n [] P"
| "restrict' 0       cs P =  P cs"
| "restrict' (Suc n) cs P =  \<nu> a. restrict' n (cs @ [a]) P"

lemma weak_proper_restrict'_preservation: "(\<And>cs. P cs \<approx>\<^sub>\<sharp> Q cs) \<Longrightarrow> restrict' n cs P \<approx>\<^sub>\<sharp> restrict' n cs Q"
proof (induction n arbitrary: cs)
  case 0
  have "restrict' 0 cs P = P cs"
    by (rule restrict'.simps(1))
  also have "... \<approx>\<^sub>\<sharp> Q cs"
    by (rule "0.prems")
  also have "... = restrict' 0 cs Q"
    by (simp add: restrict'.simps(1))
  finally show ?case
    by simp
next
  case (Suc n)
  then have "restrict' (Suc n) cs P = \<nu> a. restrict' n (cs @ [a]) P"
    by (simp add: restrict'.simps(2))
  also have "... \<approx>\<^sub>\<sharp> \<nu> a. restrict' n (cs @ [a]) Q"
    using weak_proper_new_channel_preservation by (simp add: Suc.IH Suc.prems)
  finally show ?case
    by (simp add: restrict'.simps(2))
qed

lemma weak_proper_restrict_preservation: "(\<And>cs. P cs \<approx>\<^sub>\<sharp> Q cs) \<Longrightarrow> restrict n P \<approx>\<^sub>\<sharp> restrict n Q"
  by (simp add: weak_proper_restrict'_preservation)

(* TODO: Move the following code to the corresponding theories. *)

corec repeat :: "process \<Rightarrow> process" ("\<star>_" [100] 100) where
  "\<star>p = p \<parallel> \<star>p"

lemma repeat_compatibility: "p \<sim>\<^sub>\<sharp> q \<Longrightarrow> \<star>p \<sim>\<^sub>\<sharp> \<star>q"
  sorry

lemma repeat_idempotence: "\<star>p \<parallel> \<star>p \<sim>\<^sub>\<sharp> \<star>p"
  sorry

lemma repeat_parallel_distributivity: "\<star>(p \<parallel> q) \<sim>\<^sub>\<sharp> \<star>p \<parallel> \<star>q"
  sorry

abbreviation unreliable_unicast :: "chan \<Rightarrow> process" ("\<currency>_" [1000] 1000) where
  "\<currency>a \<equiv> \<star>a \<triangleright> _. \<zero>"

abbreviation unreliable_broadcast :: "chan \<Rightarrow> process" ("\<currency>\<^sup>*_" [1000] 1000) where
  "\<currency>\<^sup>*a \<equiv> \<star>a \<triangleright> _. \<zero> \<parallel> \<star>a \<triangleright> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x)"

lemma unreliable_unicast_idempotence: "\<currency>a \<parallel> \<currency>a \<sim>\<^sub>\<sharp> \<currency>a"
  using repeat_idempotence by blast

lemma unreliable_broadcast_idempotence: "\<currency>\<^sup>*a \<parallel> \<currency>\<^sup>*a \<sim>\<^sub>\<sharp> \<currency>\<^sup>*a"
  sorry

lemma unreliable_broadcast_swallows_unreliable_unicast: "\<currency>a \<parallel> \<currency>\<^sup>*a \<sim>\<^sub>\<sharp> \<currency>\<^sup>*a"
  sorry

end
