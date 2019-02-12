section \<open>Utilities\<close>

theory Utilities
  imports
    Chi_Calculus.Processes
    Chi_Calculus.Proper_Weak_Bisimulation
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
        then show "\<exists>e. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ e \<and> proper_lift ?\<R> d e"
        proof -
          have "d = \<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)"
            using `p \<rightarrow>\<^sub>\<sharp> d` and `p = p0 y P` and transitions_from_p0 by (metis theI_unique)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> q"
            using weak_proper_transition_refl_intro by simp
          moreover have "?\<R> (\<nu> c. (\<zero> \<parallel> P y)) q"
            using aux3 and bisim_rel.id and `q = p1 y P` and p1_def by (simp add: reflpI)
          then have "proper_lift ?\<R> d (\<lparr>\<tau>\<rparr> q)"
            using simple_lift and `d = \<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)` by simp
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
        then show "\<exists>e. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ e \<and> proper_lift ?\<R> d e"
        proof cases
          case (simple \<delta> p')
          then show ?thesis
          proof -
            have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<delta>\<rparr> \<nu> c. (\<zero> \<parallel> p')"
            proof -
              have "q \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)"
                using transitions_from_p0 and `q = p0 y P` by (metis theI2)
              moreover have "\<nu> c. (\<zero> \<parallel> P y) \<Longrightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> \<nu> c. (\<zero> \<parallel> p')"
              proof -
                have "\<zero> \<parallel> P y \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<zero> \<parallel> p'"
                  using `p \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> p'` and `p = p1 y P` and p1_def and acting_right by simp
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
            moreover have "proper_lift ?\<R> (\<lparr>\<delta>\<rparr> p') (\<lparr>\<delta>\<rparr> \<nu> c. (\<zero> \<parallel> p'))"
            proof -
              have "?\<R> p' (\<nu> c. (\<zero> \<parallel> p'))"
                using aux3 and bisim_rel.id by (simp add: reflpI)
              then show ?thesis
                using simple_lift by simp
            qed
            ultimately show ?thesis
              using `d = \<lparr>\<delta>\<rparr> p'` by auto
          qed
        next
          case (output_without_opening a x p')
          then show ?thesis
          proof -
            have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleleft> x\<rparr> \<nu> c. (\<zero> \<parallel> p')"
            proof -
              have "q \<Rightarrow>\<^sup>\<tau> \<nu> c. (\<zero> \<parallel> P y)"
                using aux2 and `q = p0 y P` by simp
              moreover have "\<nu> c. (\<zero> \<parallel> P y) \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<nu> c. (\<zero> \<parallel> p')"
              proof -
                have "\<zero> \<parallel> P y \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<zero> \<parallel> p'"
                  using `p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> p'` and `p = p1 y P` and p1_def and acting_right by simp
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
            moreover have "proper_lift ?\<R> (\<lparr>a \<triangleleft> x\<rparr> p') (\<lparr>a \<triangleleft> x\<rparr> \<nu> c. (\<zero> \<parallel> p'))"
            proof -
              have "?\<R> p' (\<nu> c. (\<zero> \<parallel> p'))"
                using aux3 and bisim_rel.id by (simp add: reflpI)
              then have "output_rest_lift ?\<R> (x\<rparr> p') (x\<rparr> \<nu> c. (\<zero> \<parallel> p'))"
                using without_opening_lift by simp
              then show ?thesis
                using output_lift by simp
            qed
            ultimately show ?thesis
              using `d = \<lparr>a \<triangleleft> x\<rparr> p'` by auto
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
(* NOTE: The existing `comm_monoid` does not work because `(=)` is used, whereas `(process, \<parallel>, \<zero>)` is
   a commutative monoid when `(\<sim>\<^sub>\<sharp>)` or `(\<approx>\<^sub>\<sharp>)` is used. *)

definition
  big_parallel :: "['a \<Rightarrow> process, 'a list] \<Rightarrow> process"
where
  "big_parallel f xs \<equiv> foldr (\<lambda>x p. f x \<parallel> p) xs \<zero>"

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

(* `restrict n P` builds the process `\<nu> a\<^sub>1 ... a\<^sub>n. P [a\<^sub>1, ..., a\<^sub>n]` *)

fun
  restrict  :: "[nat, chan list \<Rightarrow> process] \<Rightarrow> process"
and
  restrict' :: "[nat, chan list, chan list \<Rightarrow> process] \<Rightarrow> process"
where
  "restrict  n          P =  restrict' n [] P"
| "restrict' 0       cs P =  P cs"
| "restrict' (Suc n) cs P =  \<nu> a. restrict' n (cs @ [a]) P"

end
