section \<open>Utilities\<close>

theory Utilities
  imports
    Chi_Calculus.Processes
    Chi_Calculus.Proper_Weak_Bisimulation
begin

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
          proof -
            have "\<nu> c. (\<zero> \<parallel> P y) \<sim>\<^sub>\<sharp> P y"
            proof -
              have "\<zero> \<parallel> P y \<sim>\<^sub>\<sharp> P y"
                using proper_parallel_unit by simp
              then have "\<nu> c. (\<zero> \<parallel> P y) \<sim>\<^sub>\<sharp> \<nu> c. P y"
                using proper_new_channel_preservation by simp
              then show ?thesis
                using proper_scope_redundancy and proper.bisimilarity_transitivity_rule by blast
            qed
            then show ?thesis
              using bisim_rel.id and `q = p1 y P` and p1_def by auto
          qed
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
        proof (cases d)
          case (Simple \<delta> p')
          then show ?thesis
          proof -
            let ?e = "\<lparr>\<delta>\<rparr> \<nu> c. (\<zero> \<parallel> p')"
            have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ ?e"
            proof -
              have "q \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> \<nu> c. (\<zero> \<parallel> P y)"
                using `q = p0 y P` and transitions_from_p0 by (metis theI_unique)
              moreover have "\<nu> c. (\<zero> \<parallel> P y) \<rightarrow>\<^sub>\<sharp> ?e"
              proof -
                have "P y \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> p'"
                  using `p \<rightarrow>\<^sub>\<sharp> d` and `d = \<lparr>\<delta>\<rparr> p'` and `p = p1 y P` and p1_def and proper_simple_trans_is_basic_trans by simp
                then have "\<zero> \<parallel> P y \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<zero> \<parallel> p'"
                  using acting_right by simp
                moreover have "\<nu> c. (\<zero> \<parallel> P y) \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> c\<rbrace> \<zero> \<parallel> P y"
                  using opening by simp
                ultimately have "\<nu> c. (\<zero> \<parallel> P y) \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> c. (\<zero> \<parallel> p')"
                  using scoped_acting by simp
                then show ?thesis
                  using proper_transition.simple by simp
              qed
              ultimately show ?thesis
                using weak_tau_respecting_proper_transition_single_simple
                  and prepend_tau_transition_to_weak_proper_transition
                  and weak_proper_transition_step_intro
                   by simp
            qed
            moreover have "proper_lift ?\<R> d ?e"
            proof -
              have "p' \<sim>\<^sub>\<sharp> \<zero> \<parallel> p'"
                using proper_parallel_unit by simp
              also have "\<zero> \<parallel> p' \<sim>\<^sub>\<sharp> \<nu> c. (\<zero> \<parallel> p')"
                using proper_scope_redundancy by simp
              finally have "p' \<sim>\<^sub>\<sharp> \<nu> c. (\<zero> \<parallel> p')" .
              then have "?\<R> p' (\<nu> c. (\<zero> \<parallel> p'))"
                using bisim_rel.id by auto
              then show ?thesis
                using simple_lift and `d = \<lparr>\<delta>\<rparr> p'` by simp
            qed
            ultimately show ?thesis
              by smt
          qed
        next
          case (Output c K)
          then show ?thesis
          proof (induction K)
            case (WithoutOpening x p)
            then show ?case sorry
          next
            case (WithOpening \<F>)
            then show ?case sorry
          qed
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

end
