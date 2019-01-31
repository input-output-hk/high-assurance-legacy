section \<open>Broadcast-involving Examples\<close>

theory Broadcaster_Examples
  imports
    Chi_Calculus.Processes
    Chi_Calculus.Proper_Weak_Bisimulation
    Chi_Calculus_Examples.Utilities
    "HOL-Library.BNF_Corec"
begin

subsection \<open>Example 1: The following is a "warm-up" example. It uses recursion and input prefix only. \<close>
context
begin

private primcorec
  ex1_p :: "chan \<Rightarrow> process"
where
  "ex1_p a = a \<triangleright> _. ex1_p a"

private corec
  ex1_q :: "chan \<Rightarrow> process"
where
  "ex1_q a = a \<triangleright> _. a \<triangleright> _. ex1_q a"

private inductive
  ex1_bisim_rel :: "[process, process] \<Rightarrow> bool"
where
  p0_q0: "ex1_bisim_rel (ex1_p a) (ex1_q a)" |
  p0_q1: "ex1_bisim_rel (ex1_p a) (a \<triangleright> _. ex1_q a)" |
  q0_p0: "ex1_bisim_rel (ex1_q a) (ex1_p a)" |
  q1_p0: "ex1_bisim_rel (a \<triangleright> _. ex1_q a) (ex1_p a)"

theorem ex1_bisim: "ex1_p a \<approx>\<^sub>\<sharp> ex1_q a"
proof -
  have "ex1_bisim_rel (ex1_p a) (ex1_q a)"
    using ex1_bisim_rel.p0_q0 by simp
  then show ?thesis
  proof (coinduct rule: weak_proper_bisim_proof_method)
    case (sim p' q')
    then show ?case
    proof cases
      case (p0_q0 a)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p' \<rightarrow>\<^sub>\<sharp> c"
        then obtain x where "c = \<lparr>a \<triangleright> x\<rparr> ex1_p a"
          using \<open>p' = ex1_p a\<close> and proper_transitions_from_receive and ex1_p.code by metis
        then show "\<exists>d. q' \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ex1_bisim_rel c d"
        proof (intro exI[of _ "\<lparr>a \<triangleright> x\<rparr> a \<triangleright> _. ex1_q a"] conjI)
          show "q' \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleright> x\<rparr> a \<triangleright> _. ex1_q a"
          proof -
            have "q' \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> a \<triangleright> _. ex1_q a"
              using \<open>q' = ex1_q a\<close> and receiving and ex1_q.code by metis
            then have "q' \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> a \<triangleright> _. ex1_q a"
              using proper_transition.simple and basic_action_of.simps(1) by simp
            then have "q' \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> a \<triangleright> _. ex1_q a"
              using weak_tau_respecting_proper_transition_single_simple by simp
            then show ?thesis
              using weak_proper_transition_def by simp
          qed
        next
          show "proper_lift ex1_bisim_rel c (\<lparr>a \<triangleright> x\<rparr> a \<triangleright> _. ex1_q a)"
          proof -
            have "ex1_bisim_rel (ex1_p a) (a \<triangleright> _. ex1_q a)"
              using p0_q1 by simp
            then show ?thesis
              using simple_lift and \<open>c = \<lparr>a \<triangleright> x\<rparr> ex1_p a\<close> by simp
          qed
        qed
      qed
    next
      case (p0_q1 a)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p' \<rightarrow>\<^sub>\<sharp> c"
        then obtain x where "c = \<lparr>a \<triangleright> x\<rparr> ex1_p a"
          using \<open>p' = ex1_p a\<close> and proper_transitions_from_receive and ex1_p.code by metis
        then show "\<exists>d. q' \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ex1_bisim_rel c d"
        proof (intro exI[of _ "\<lparr>a \<triangleright> x\<rparr> ex1_q a"] conjI)
          show "q' \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleright> x\<rparr> ex1_q a"
          proof -
            have "q' \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> ex1_q a"
              using \<open>q' = a \<triangleright> _. ex1_q a\<close> by (blast intro: receiving)
            then have "q' \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> ex1_q a"
              using proper_transition.simple and basic_action_of.simps(1) by simp
            then have "q' \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> ex1_q a"
              using weak_tau_respecting_proper_transition_single_simple by simp
            then show ?thesis
              using weak_proper_transition_def by simp
          qed
        next
          show "proper_lift ex1_bisim_rel c (\<lparr>a \<triangleright> x\<rparr> ex1_q a)"
          proof -
            have "ex1_bisim_rel (ex1_p a) (ex1_q a)"
              using p0_q0 by simp
            then show ?thesis
              using simple_lift and \<open>c = \<lparr>a \<triangleright> x\<rparr> ex1_p a\<close> by simp
          qed
        qed
      qed
    next
      case (q0_p0 a)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p' \<rightarrow>\<^sub>\<sharp> c"
        then obtain x where "c = \<lparr>a \<triangleright> x\<rparr> a \<triangleright> _. ex1_q a"
          using \<open>p' = ex1_q a\<close> and proper_transitions_from_receive and ex1_q.code by metis
        then show "\<exists>d. q' \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ex1_bisim_rel c d"
        proof (intro exI[of _ "\<lparr>a \<triangleright> x\<rparr> ex1_p a"] conjI)
          show "q' \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleright> x\<rparr> ex1_p a"
          proof -
            have "q' \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> ex1_p a" 
              using \<open>q' = ex1_p a\<close> and ex1_p.code and receiving by metis
            then have "q' \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> ex1_p a"
              using proper_transition.simple and basic_action_of.simps(1) by simp
            then have "q' \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> ex1_p a"
              using weak_tau_respecting_proper_transition_single_simple by simp
            then show ?thesis
              using weak_proper_transition_def by simp
          qed
        next
          show "proper_lift ex1_bisim_rel c (\<lparr>a \<triangleright> x\<rparr> ex1_p a)"
          proof -
            have "ex1_bisim_rel (a \<triangleright> _. ex1_q a) (ex1_p a)"
              using q1_p0 by simp
            then show ?thesis
              using simple_lift and \<open>c = \<lparr>a \<triangleright> x\<rparr> a \<triangleright> _. ex1_q a\<close> by simp
          qed
        qed
      qed
    next
      case (q1_p0 a)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p' \<rightarrow>\<^sub>\<sharp> c"
        then obtain x where "c = \<lparr>a \<triangleright> x\<rparr> ex1_q a"
          using \<open>p' = a \<triangleright> _. ex1_q a\<close> and proper_transitions_from_receive by metis
        then show "\<exists>d. q' \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ex1_bisim_rel c d"
        proof (intro exI[of _ "\<lparr>a \<triangleright> x\<rparr> ex1_p a"] conjI)
          show "q' \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>a \<triangleright> x\<rparr> ex1_p a"
          proof -
            have "q' \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> ex1_p a"
              using \<open>q' = ex1_p a\<close> and ex1_p.code and receiving by metis
            then have "q' \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> ex1_p a"
              using proper_transition.simple and basic_action_of.simps(1) by simp
            then have "q' \<Longrightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> ex1_p a"
              using weak_tau_respecting_proper_transition_single_simple by simp
            then show ?thesis
              using weak_proper_transition_def by simp
          qed
        next
          show "proper_lift ex1_bisim_rel c (\<lparr>a \<triangleright> x\<rparr> ex1_p a)"
          proof -
            have "ex1_bisim_rel (ex1_q a) (ex1_p a)"
              using q0_p0 by simp
            then show ?thesis
              using simple_lift and \<open>c = \<lparr>a \<triangleright> x\<rparr> ex1_q a\<close> by simp
          qed
        qed
      qed
    qed
  next
    case (sym p q)
    then show ?case
      using ex1_bisim_rel.simps by blast
  qed
qed

end

end
