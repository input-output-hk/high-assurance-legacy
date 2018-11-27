theory Communication_Medium
  imports
    (* "HOL-Library.BNF_Corec" *)
    Chi_Calculus.Processes
    Chi_Calculus.Proper_Weak_Bisimulation
begin

(*
corec
  sender :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "sender inp inpm = inp \<triangleright>\<degree> x. (inpm \<triangleleft>\<degree> x \<parallel> sender inp inpm)"
*)

definition
  sender
where
  "sender inp inpm \<equiv> inp \<triangleright> x. inpm \<triangleleft> x"

(*
corec
  receiver :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "receiver outm out = outm  \<triangleright>\<degree> x. (out \<triangleleft>\<degree> x \<parallel> receiver outm out)"
*)

definition
  receiver
where
  "receiver outm out \<equiv> outm \<triangleright> x. out \<triangleleft> x"

(*
corec
  medium :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "medium inpm outm = inpm \<triangleright>\<degree> x. (outm \<triangleleft>\<degree> x \<parallel> medium inpm outm)"
*)

definition
  medium
where
  "medium inpm outm \<equiv> inpm \<triangleright> x. outm \<triangleleft> x"

abbreviation
  impl
where
  "impl inp out \<equiv> \<nu> inpm outm. (sender inp inpm \<parallel> medium inpm outm \<parallel> receiver outm out)"

(*
corec
  spec :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "spec inp out = inp \<triangleright>\<degree> x. (out \<triangleleft>\<degree> x \<parallel> spec inp out)"
*)

abbreviation
  spec
where
  "spec inp out \<equiv> inp \<triangleright> x. out \<triangleleft> x"

(** Auxiliary lemmas **)

lemma proper_output_is_basic_sending: "p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q \<Longrightarrow> p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q"
  using proper_transition.simps by blast

lemma proper_sending: "a \<triangleleft> x \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<zero>"
  using sending and proper_transition.output_without_opening by simp

lemma proper_output_without_opening_res: "(\<And>b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> Q b) \<Longrightarrow> \<nu> b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> \<nu> b. Q b"
  using acting_scope proper_transition.output_without_opening and proper_output_is_basic_sending by simp

lemma no_simple_transitions_from_output: "\<not> a \<triangleleft> x \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q"
  by (metis basic_transitions_from_send basic_action.distinct(1) basic_action.inject basic_action_of.simps(1) basic_action_of.simps(2) basic_residual.inject(1) io_action.distinct(1) proper_action.exhaust proper_residual.distinct(1) proper_transition.simps)

lemma no_opening_transitions_from_output: "\<not> a \<triangleleft> x \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> a. K a"
  by (metis no_opening_transitions_from_send no_simple_transitions_from_output output_rest.distinct(1) proper_residual.inject(2) proper_transition.cases)

lemma proper_transitions_from_output: "a \<triangleleft> x \<rightarrow>\<^sub>\<sharp> c \<Longrightarrow> c = \<lparr>a \<triangleleft> x\<rparr> \<zero>"
proof (induction "a \<triangleleft> x :: process" c rule: proper_transition.induct)
  case simple
  then show ?case
    using no_simple_transitions_from_output and proper_transition.simple by blast
next
  case output_without_opening
  then show ?case
    using no_opening_transitions_from_send and basic_transitions_from_send by fastforce
next
  case output_with_opening
  then show ?case using no_opening_transitions_from_output
    by (simp add: no_opening_transitions_from_send)
qed

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

lemma basic_communication_ltr: "a \<triangleleft> x \<parallel> a \<triangleright> x. P x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> P x"
  using basic_transition.intros(2) communication ltr sending by blast

(** Bisimulation relation. **)

inductive
  bisim_rel :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  p1_q1: "
    bisim_rel (impl inp out) (spec inp out)" |
  q1_p1: "
    bisim_rel (spec inp out) (impl inp out)" |
  p2_q2: "
    bisim_rel (\<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)) (out \<triangleleft> x)" |
  q2_p2: "
    bisim_rel (out \<triangleleft> x) (\<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out))" |
  p3_q2: "
    bisim_rel (\<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out)) (out \<triangleleft> x)" |
  q2_p3: "
    bisim_rel (out \<triangleleft> x) (\<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out))" |
  p4_q2_and_q2_p4: "
    bisim_rel (out \<triangleleft> x) (out \<triangleleft> x)" |
  p5_q3_and_q3_p5: "
    bisim_rel \<zero> \<zero>"

(** Correctness proof. **)

(* TODO: Prove it. *)
lemma transitions_from_p1: "impl inp out \<rightarrow>\<^sub>\<sharp> c \<Longrightarrow> c = \<lparr>inp \<triangleright> x\<rparr> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)"
  sorry

(* TODO: Prove it. *)
lemma transitions_from_p2: "\<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out) \<rightarrow>\<^sub>\<sharp> c \<Longrightarrow> c = \<lparr>\<tau>\<rparr> \<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out)"
  sorry

(* TODO: Prove it. *)
lemma transitions_from_p3: "\<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out) \<rightarrow>\<^sub>\<sharp>c \<Longrightarrow> c = \<lparr>\<tau>\<rparr> \<nu> outm. (\<zero> \<parallel> out \<triangleleft> x)"
proof -
  fix c
  assume "\<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out) \<rightarrow>\<^sub>\<sharp>c"
  then show "c = \<lparr>\<tau>\<rparr> \<nu> outm. (\<zero> \<parallel> out \<triangleleft> x)"
  proof (induction "\<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out)" c)
  case (simple \<delta> q)
  then show ?case
  proof cases
    case (scoped_acting Q R)
    then show ?thesis sorry
  qed
  next
  case (output_without_opening a x q)
    then show ?case sorry
  next
    case (output_with_opening Q a K)
    then show ?case sorry
  qed
qed

(* TODO: Prove it. *)
lemma transitions_from_p4: "\<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> out \<triangleleft> x) \<rightarrow>\<^sub>\<sharp> c \<Longrightarrow> c = \<lparr>\<tau>\<rparr> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>)"
  sorry

(* TODO: Prove it. *)
lemma transitions_from_q1:
  assumes "spec inp out \<rightarrow>\<^sub>\<sharp> c"
  obtains x where "c = \<lparr>inp \<triangleright> x\<rparr> out \<triangleleft> x"
  using assms and proper_transitions_from_receive by force

theorem correctness: "impl inp out \<approx>\<^sub>\<sharp> spec inp out"
proof -
  let ?\<R> = "(\<sim>\<^sub>\<sharp>) OO bisim_rel OO (\<sim>\<^sub>\<sharp>)"
  have "bisim_rel (impl inp out) (spec inp out)"
    using p1_q1 by simp
  then show ?thesis
  proof (coinduct rule: weak_proper_bisim_up_to_strong_bisim)
    case (sim p q)
    then show ?case
    proof cases
      case (p1_q1 inp out)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p \<rightarrow>\<^sub>\<sharp> c"
        then show "\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ?\<R> c d"
        proof -
          (* The only possible transition from p is p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out). *)
          obtain x where "c = \<lparr>inp \<triangleright> x\<rparr> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)"
            using `p \<rightarrow>\<^sub>\<sharp> c` and `p = impl inp out` and transitions_from_p1 by simp
          (* There is a simulating weak transition from Q, namely Q \<Longrightarrow>\<^sub>\<sharp>\<lparr>inp \<triangleright> x\<rparr> out \<triangleleft> x. *)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>inp \<triangleright> x\<rparr> out \<triangleleft> x"
            using `q = spec inp out` and weak_proper_transition_receiving by simp
          (* And the derivatives (namely \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out) and out \<triangleleft> x) are related. *)
          moreover have "proper_lift ?\<R> c (\<lparr>inp \<triangleright> x\<rparr> out \<triangleleft> x)"
          proof -
            have "?\<R> (\<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)) (out \<triangleleft> x)"
              using p2_q2 by auto
            then show ?thesis
              using `c = \<lparr>inp \<triangleright> x\<rparr> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)` and simple_lift by simp
          qed
          ultimately show ?thesis
            using `q = spec inp out` by auto
        qed
      qed
    next
      case (q1_p1 inp out)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p \<rightarrow>\<^sub>\<sharp> c"
        then show "\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ?\<R> c d"
        proof -
          (* The only possible transition from p is p \<rightarrow>\<^sub>\<sharp>\<lparr>inp \<triangleright> x\<rparr> out \<triangleleft> x. *)
          obtain x where "c = \<lparr>inp \<triangleright> x\<rparr> out \<triangleleft> x"
            using `p \<rightarrow>\<^sub>\<sharp> c` and `p = spec inp out` and transitions_from_q1 by force
          (* There is a simulating weak transition from q, namely q \<Longrightarrow>\<^sub>\<sharp>\<lparr>inp \<triangleright> x\<rparr> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out). *)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>inp \<triangleright> x\<rparr> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)"
          proof -
            have "q \<rightarrow>\<^sub>\<sharp>\<lparr>inp \<triangleright> x\<rparr> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)"
            proof -
              have "q \<rightarrow>\<^sub>\<flat>\<lbrace>inp \<triangleright> x\<rbrace> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)"
              proof -
                have "\<And>inpm. sender inp inpm \<rightarrow>\<^sub>\<flat>\<lbrace>inp \<triangleright> x\<rbrace> inpm \<triangleleft> x"
                  using sender_def and receiving by simp
                then have "\<And>inpm outm. sender inp inpm \<parallel> medium inpm outm \<parallel> receiver outm out \<rightarrow>\<^sub>\<flat>\<lbrace>inp \<triangleright> x\<rbrace> inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out"
                  using acting_left by simp
                then show ?thesis
                  using acting_scope and `q = impl inp out` by simp
              qed
              then show ?thesis
                using proper_transition.simple by simp
            qed
            then show ?thesis
              using weak_proper_transition_single_simple by simp
          qed
          (* And the derivatives (namely out \<triangleleft> x and \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)) are related. *)
          moreover have "proper_lift ?\<R> c (\<lparr>inp \<triangleright> x\<rparr> \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out))"
          proof -
            have "?\<R> (out \<triangleleft> x) (\<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out))"
              using q2_p2 by auto
            then show ?thesis
              using `c = \<lparr>inp \<triangleright> x\<rparr> out \<triangleleft> x` and simple_lift by simp
          qed
          ultimately show ?thesis
            using `q = impl inp out` by auto
        qed
      qed
    next
      case (p2_q2 x out)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p \<rightarrow>\<^sub>\<sharp> c"
        then show "\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ?\<R> c d"
        proof -
          (* The only possible transition from p is p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> \<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out). *)
          have "c = \<lparr>\<tau>\<rparr> \<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out)"
            using `p \<rightarrow>\<^sub>\<sharp> c` and `p = \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)` and transitions_from_p2 by simp
          (* There is a simulating weak transition from q, namely q \<Longrightarrow>\<^sub>\<sharp> q. *)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> q"
            using weak_proper_transition_refl_intro by simp
          (* And the derivatives (namely \<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out) and q) are related. *)
          moreover have "proper_lift ?\<R> c (\<lparr>\<tau>\<rparr> q)"
          proof -
            have "?\<R> (\<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out)) q"
            proof -
              have "bisim_rel (\<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out)) q"
                using `q = out \<triangleleft> x` and p3_q2 by simp
              moreover have "\<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out) \<sim>\<^sub>\<sharp> \<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out)"
              proof -
                have "\<And>outm. \<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out \<sim>\<^sub>\<sharp> outm \<triangleleft> x \<parallel> receiver outm out"
                  using proper_parallel_unit by simp
                then have "\<nu> outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out) \<sim>\<^sub>\<sharp> \<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out)"
                  using proper_new_channel_preservation by simp
                moreover have "\<nu> outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out) \<sim>\<^sub>\<sharp> \<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out)"
                  using proper_scope_redundancy by simp
                ultimately show ?thesis
                  using proper.bisimilarity_transitivity_rule by blast
              qed
              ultimately show ?thesis
                by auto
            qed
            then show ?thesis
              using `c = \<lparr>\<tau>\<rparr> \<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out)` and simple_lift by simp
          qed
          ultimately show ?thesis
            using `q = out \<triangleleft> x` by auto
        qed
      qed
    next
      case (q2_p2 out x)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p \<rightarrow>\<^sub>\<sharp> c"
        then show "\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ?\<R> c d"
        proof -
          (* The only possible transition from p is p \<rightarrow>\<^sub>\<sharp>\<lparr>out \<triangleleft> x\<rparr> \<zero>. *)
          have "c = \<lparr>out \<triangleleft> x\<rparr> \<zero>"
            using `p \<rightarrow>\<^sub>\<sharp> c` and `p = out \<triangleleft> x` and proper_transitions_from_output by simp
          (* There is a simulating weak transition from q, namely q \<Longrightarrow>\<^sub>\<sharp>^\<lparr>out \<triangleleft> x\<rparr> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>). *)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>out \<triangleleft> x\<rparr> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>)"
          proof -
            have "q \<Longrightarrow>\<^sub>\<sharp>\<lparr>out \<triangleleft> x\<rparr> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>)"
            proof -
              have "q \<Rightarrow>\<^sup>\<tau> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> out \<triangleleft> x)"
              proof -
                have "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out)"
                proof -
                  have "\<And>inpm outm. inpm \<triangleleft> x \<parallel> medium inpm outm \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> outm \<triangleleft> x"
                    using basic_communication_ltr and medium_def by simp
                  then have "\<And>inpm outm. inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out"
                    by (metis acting_left communication ltr medium_def receiving sending) (* FIXME: Why not just acting_left? *)
                  then show ?thesis
                    using acting_scope and `q = \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)` by simp
                qed
                moreover have "\<nu> inpm outm. (\<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out) \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> out \<triangleleft> x)"
                proof -
                  have "\<And>inpm outm. outm \<triangleleft> x \<parallel> receiver outm out \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> out \<triangleleft> x"
                    using basic_communication_ltr and receiver_def by simp
                  then have "\<And>inpm outm. \<zero> \<parallel> outm \<triangleleft> x \<parallel> receiver outm out \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> \<zero> \<parallel> out \<triangleleft> x"
                    using acting_right by simp
                  then show ?thesis
                    using acting_scope by simp
                qed
                ultimately show ?thesis
                  using tau_transition_is_tau_sequence and append_tau_transition_to_tau_sequence_is_tau_sequence by fastforce
              qed
              moreover have "\<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> out \<triangleleft> x) \<rightarrow>\<^sub>\<sharp>\<lparr>out \<triangleleft> x\<rparr> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>)"
              proof -
                have "out \<triangleleft> x \<rightarrow>\<^sub>\<flat>\<lbrace>out \<triangleleft> x\<rbrace> \<zero>"
                  using sending by simp
                then have "\<zero> \<parallel> \<zero> \<parallel> out \<triangleleft> x \<rightarrow>\<^sub>\<flat>\<lbrace>out \<triangleleft> x\<rbrace> \<zero> \<parallel> \<zero> \<parallel> \<zero>"
                  using acting_right by simp
                then show ?thesis
                  using acting_scope and proper_transition.output_without_opening by simp
              qed
              ultimately show ?thesis
                using weak_tau_respecting_proper_transition.output_without_opening by fastforce
            qed
            then show ?thesis
              using weak_proper_transition_def by simp
          qed
          (* And the derivatives (namely \<zero> and \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>) are related. *)
          moreover have "proper_lift ?\<R> c (\<lparr>out \<triangleleft> x\<rparr> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>))"
          proof -
            have "bisim_rel \<zero> \<zero>"
              using p5_q3_and_q3_p5 by simp
            moreover have "\<zero> \<sim>\<^sub>\<sharp> \<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>)"
              using proper_scope_redundancy and proper_parallel_unit and proper.bisimilarity_transitivity_rule by meson
            ultimately have "?\<R> \<zero> (\<nu> inpm outm. (\<zero> \<parallel> \<zero> \<parallel> \<zero>))"
              using proper.bisimilarity_reflexivity_rule by auto
            then show ?thesis
              using `c = \<lparr>out \<triangleleft> x\<rparr> \<zero>` and output_lift and without_opening_lift by simp
          qed
          ultimately show ?thesis
            using `q = \<nu> inpm outm. (inpm \<triangleleft> x \<parallel> medium inpm outm \<parallel> receiver outm out)` by fastforce
        qed
      qed
    next
      case (p3_q2 x out)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p \<rightarrow>\<^sub>\<sharp> c"
        then show "\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ?\<R> c d"
        proof -
          (* The only possible transition from p is p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> \<nu> outm. (\<zero> \<parallel> out \<triangleleft> x). *)
          have "c = \<lparr>\<tau>\<rparr> \<nu> outm. (\<zero> \<parallel> out \<triangleleft> x)"
            using `p \<rightarrow>\<^sub>\<sharp> c` and `p = \<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out)` and transitions_from_p3 by simp
          (* There is a simulating weak transition from q, namely q \<Longrightarrow>\<^sub>\<sharp> q. *)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>\<tau>\<rparr> q"
            using weak_proper_transition_refl_intro by simp
          (* And the derivatives (namely \<nu> outm. (\<zero> \<parallel> out \<triangleleft> x) and q) are related. *)
          moreover have "proper_lift ?\<R> c (\<lparr>\<tau>\<rparr> out \<triangleleft> x)"
          proof -
            have "bisim_rel (out \<triangleleft> x) (out \<triangleleft> x)"
              using p4_q2_and_q2_p4 by simp
            moreover have "\<nu> outm. (\<zero> \<parallel> out \<triangleleft> x) \<sim>\<^sub>\<sharp> out \<triangleleft> x"
              using proper_scope_redundancy and proper_parallel_unit and proper.bisimilarity_transitivity_rule by meson
            ultimately have "?\<R> (\<nu> outm. (\<zero> \<parallel> out \<triangleleft> x)) (out \<triangleleft> x)"
              using proper.bisimilarity_reflexivity_rule by auto
            then show ?thesis
              using `c = \<lparr>\<tau>\<rparr> \<nu> outm. (\<zero> \<parallel> out \<triangleleft> x)` and simple_lift by simp
          qed
          ultimately show ?thesis
            using `q = out \<triangleleft> x` by fastforce
        qed
      qed
    next
      case (q2_p3 out x)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p \<rightarrow>\<^sub>\<sharp> c"
        then show "\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ?\<R> c d"
        proof -
          (* The only possible transition from p is p \<rightarrow>\<^sub>\<sharp>\<lparr>out \<triangleleft> x\<rparr> \<zero>. *)
          have "c = \<lparr>out \<triangleleft> x\<rparr> \<zero>"
            using `p \<rightarrow>\<^sub>\<sharp> c` and `p = out \<triangleleft> x` and proper_transitions_from_output by simp
          (* There is a simulating weak transition from q, namely q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>out \<triangleleft> x\<rparr> \<nu> outm. (\<zero> \<parallel> \<zero>). *)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>out \<triangleleft> x\<rparr> \<nu> outm. (\<zero> \<parallel> \<zero>)"
          proof -
            have "q \<Longrightarrow>\<^sub>\<sharp>\<lparr>out \<triangleleft> x\<rparr> \<nu> outm. (\<zero> \<parallel> \<zero>)"
            proof -
              have "q \<Rightarrow>\<^sup>\<tau> \<nu> outm. (\<zero> \<parallel> out \<triangleleft> x)"
              proof -
                have "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> outm. (\<zero> \<parallel> out \<triangleleft> x)"
                proof -
                  have "\<And>outm. outm \<triangleleft> x \<parallel> receiver outm out \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero> \<parallel> out \<triangleleft> x"
                    using basic_communication_ltr and receiver_def by simp
                 then show ?thesis
                    using acting_scope and `q = \<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out)` by simp
                qed
                then show ?thesis
                  using tau_transition_is_tau_sequence by fastforce
              qed
              moreover have "\<nu> outm. (\<zero> \<parallel> out \<triangleleft> x) \<rightarrow>\<^sub>\<sharp>\<lparr>out \<triangleleft> x\<rparr> \<nu> outm. (\<zero> \<parallel> \<zero>)"
              proof -
                have "out \<triangleleft> x \<rightarrow>\<^sub>\<flat>\<lbrace>out \<triangleleft> x\<rbrace> \<zero>"
                  using sending by simp
                then have "\<zero> \<parallel> out \<triangleleft> x \<rightarrow>\<^sub>\<flat>\<lbrace>out \<triangleleft> x\<rbrace> \<zero> \<parallel> \<zero>"
                  using acting_right by simp
                then have "\<nu> outm. (\<zero> \<parallel> out \<triangleleft> x) \<rightarrow>\<^sub>\<flat>\<lbrace>out \<triangleleft> x\<rbrace> \<nu> outm. (\<zero> \<parallel> \<zero>)"
                  using acting_scope by simp
                then show ?thesis
                  using proper_transition.output_without_opening by simp
              qed
              ultimately show ?thesis
                using weak_tau_respecting_proper_transition.output_without_opening by fastforce
            qed
            then show ?thesis
              using weak_proper_transition_def by simp
          qed
          (* And the derivatives (namely \<zero> and \<nu> outm. (\<zero> \<parallel> \<zero>) are related. *)
          moreover have "proper_lift ?\<R> c (\<lparr>out \<triangleleft> x\<rparr> \<nu> outm. (\<zero> \<parallel> \<zero>))"
          proof -
            have "bisim_rel \<zero> \<zero>"
              using p5_q3_and_q3_p5 by simp
            moreover have "\<zero> \<sim>\<^sub>\<sharp> \<nu> outm. (\<zero> \<parallel> \<zero>)"
              using proper_scope_redundancy and proper_parallel_unit and proper.bisimilarity_transitivity_rule by meson
            ultimately have "?\<R> \<zero> (\<nu> outm. (\<zero> \<parallel> \<zero>))"
              using proper.bisimilarity_reflexivity_rule by auto
            then show ?thesis
              using `c = \<lparr>out \<triangleleft> x\<rparr> \<zero>` and output_lift and without_opening_lift by simp
          qed
          ultimately show ?thesis
            using `q = \<nu> outm. (outm \<triangleleft> x \<parallel> receiver outm out)` by fastforce
        qed
      qed
    next
      case (p4_q2_and_q2_p4 out x)
      then show ?thesis
      proof (intro impI allI)
        fix c
        assume "p \<rightarrow>\<^sub>\<sharp> c"
        then show "\<exists>d. q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^ d \<and> proper_lift ?\<R> c d"
        proof -
          (* The only possible transition from p is p \<rightarrow>\<^sub>\<sharp>\<lparr>out \<triangleleft> x\<rparr> \<zero>. *)
          have "c = \<lparr>out \<triangleleft> x\<rparr> \<zero>"
            using `p \<rightarrow>\<^sub>\<sharp> c` and `p = out \<triangleleft> x` and proper_transitions_from_output by simp
          (* There is a simulating weak transition from q, namely q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>out \<triangleleft> x\<rparr> \<zero>. *)
          moreover have "q \<Longrightarrow>\<^sub>\<sharp>\<^sup>^\<lparr>out \<triangleleft> x\<rparr> \<zero>"
            using `q = out \<triangleleft> x` and weak_proper_transition_sending by simp
          (* And the derivatives (namely \<zero> and \<zero> are related. *)
          moreover have "proper_lift ?\<R> c (\<lparr>out \<triangleleft> x\<rparr> \<zero>)"
          proof -
            have "bisim_rel \<zero> \<zero>"
              using p5_q3_and_q3_p5 by simp
            then have "?\<R> \<zero> \<zero>"
              using proper.bisimilarity_reflexivity_rule by auto
            then show ?thesis
              using `c = \<lparr>out \<triangleleft> x\<rparr> \<zero>` and output_lift and without_opening_lift by simp
          qed
          ultimately show ?thesis
            using `q = out \<triangleleft> x` by fastforce
        qed
      qed
    next
      case p5_q3_and_q3_p5
      then show ?thesis
        using no_proper_transitions_from_stop by simp
    qed
  next
    case sym
    then show ?case
    proof cases
      case p1_q1
      then show ?thesis
        using q1_p1 by simp
    next
      case q1_p1
      then show ?thesis
        using p1_q1 by simp
    next
      case p2_q2
      then show ?thesis
        using q2_p2 by simp
    next
      case q2_p2
      then show ?thesis
        using p2_q2 by simp
    next
      case p3_q2
      then show ?thesis
        using q2_p3 by simp
    next
      case q2_p3
      then show ?thesis
        using p3_q2 by simp
    next
      case p4_q2_and_q2_p4
      then show ?thesis
        using local.sym by blast
    next
      case p5_q3_and_q3_p5
      then show ?thesis
        using local.sym by blast
    qed
  qed
qed

end
