section \<open>Broadcaster Equivalences\<close>

text \<open>
  In this section We prove the equivalence between broadcasting and forwarding to peers.
\<close>

theory Broadcaster_Equivalences
  imports
    Chi_Calculus.Processes
    Chi_Calculus.Proper_Weak_Bisimulation
    Utilities
begin

text \<open>
  The following is the proof that broadcasting is observationally equivalent to a chain of
   forwarders.
\<close>

(* Chaining operator. *)

definition
  chaining_op :: "[[chan, chan] \<Rightarrow> process, [chan, chan] \<Rightarrow> process] \<Rightarrow> ([chan, chan] \<Rightarrow> process)" (infixr "\<frown>" 60)
where
  "chaining_op P Q \<equiv> \<lambda>inp out. \<nu> c. (P inp c \<parallel> Q c out)"

lemma chaining_op_associativity: "((P \<frown> Q) \<frown> R) inp out \<approx>\<^sub>\<sharp> (P \<frown> (Q \<frown> R)) inp out"
proof -
  have "((P \<frown> Q) \<frown> R) inp out \<approx>\<^sub>\<sharp> \<nu> c. \<nu> d. ((P inp d \<parallel> Q d c) \<parallel> R c out)"
  proof -
    have "((P \<frown> Q) \<frown> R) inp out = \<nu> c. ((P \<frown> Q) inp c \<parallel> R c out)"
      using chaining_op_def by simp
    also have "... = \<nu> c. (\<nu> d. (P inp d \<parallel> Q d c) \<parallel> R c out)"
      using chaining_op_def by simp
    also have "... \<approx>\<^sub>\<sharp> \<nu> c. \<nu> d. ((P inp d \<parallel> Q d c) \<parallel> R c out)"
    proof -
      have "\<And>c. \<nu> d. (P inp d \<parallel> Q d c) \<parallel> R c out \<approx>\<^sub>\<sharp> \<nu> d. ((P inp d \<parallel> Q d c) \<parallel> R c out)"
        using weak_proper_parallel_scope_extension by simp
      then show ?thesis
        using weak_proper_new_channel_preservation by simp
    qed
    finally show ?thesis .
  qed
  moreover have "(P \<frown> (Q \<frown> R)) inp out \<approx>\<^sub>\<sharp> \<nu> c. \<nu> d. (P inp d \<parallel> (Q d c \<parallel> R c out))"
  proof -
    have "(P \<frown> (Q \<frown> R)) inp out = \<nu> c. (P inp c \<parallel> (Q \<frown> R) c out)"
      using chaining_op_def by simp
    also have "... = \<nu> c. (P inp c \<parallel> \<nu> d. (Q c d \<parallel> R d out))"
      using chaining_op_def by simp
    also have "... \<approx>\<^sub>\<sharp> \<nu> c. \<nu> d. (P inp d \<parallel> (Q d c \<parallel> R c out))"
    proof -
      have "\<And>d. P inp d \<parallel> \<nu> c. (Q d c \<parallel> R c out) \<approx>\<^sub>\<sharp> \<nu> c. (P inp d \<parallel> (Q d c \<parallel> R c out))"
        using weak_proper_parallel_scope_extension2 by simp
      then have "\<nu> d. (P inp d \<parallel> \<nu> c. (Q d c \<parallel> R c out)) \<approx>\<^sub>\<sharp> \<nu> d. \<nu> c. (P inp d \<parallel> (Q d c \<parallel> R c out))"
        using weak_proper_new_channel_preservation by simp
      then show ?thesis
        using weak_proper_new_channel_scope_extension and weak_proper_bisim_transitivity by simp
    qed
    finally show ?thesis .
  qed
  moreover have "\<nu> c. \<nu> d. ((P inp d \<parallel> Q d c) \<parallel> R c out) \<approx>\<^sub>\<sharp> \<nu> c. \<nu> d. (P inp d \<parallel> (Q d c \<parallel> R c out))"
  proof -
    have "\<And>c d. (P inp d \<parallel> Q d c) \<parallel> R c out \<approx>\<^sub>\<sharp> P inp d \<parallel> (Q d c \<parallel> R c out)"
      using weak_proper_parallel_associativity by simp
    then show ?thesis
      using weak_proper_new_channel_preservation by simp
  qed
  ultimately show ?thesis
    using weak_proper_bisim_transitivity and weak_proper_bisim_symmetry by blast
qed

(* Forwarder process. *)

definition
  forwarder :: "[chan, chan, chan] \<Rightarrow> process"
where
  "forwarder dlv inp out \<equiv> inp \<triangleright> x. (dlv \<triangleleft> x \<parallel> out \<triangleleft> x)"

(* Forwarder system, namely a chain of forwarders and a sender process. *)

abbreviation
  sink :: "[chan, chan] \<Rightarrow> process"
where
  "sink inp _ \<equiv> inp \<triangleright> x. \<zero>"

definition
  chain :: "[chan list, [chan, chan, chan] \<Rightarrow> process] \<Rightarrow> ([chan, chan] \<Rightarrow> process)"
where
  "chain cs P \<equiv> foldr (\<frown>) (map P cs) sink"

definition
  forwarder_chain :: "[chan list, chan] \<Rightarrow> process"
where
  "forwarder_chain cs inp \<equiv> chain cs forwarder inp undefined"

definition
  forwarder_system :: "[chan list, val] \<Rightarrow> process"
where
  "forwarder_system cs m \<equiv> \<nu> inp. (inp \<triangleleft> m \<parallel> forwarder_chain cs inp)"

(* Broadcaster process. *)

definition
  broadcaster :: "[chan list, chan] \<Rightarrow> process"
where
  "broadcaster cs inp \<equiv> inp \<triangleright> x. (\<parallel>c \<leftarrow> cs. c \<triangleleft> x)"

(* Broadcaster system, namely a broadcaster process and a sender process. *)

definition
  broadcaster_system :: "[chan list, val] \<Rightarrow> process"
where
  "broadcaster_system cs m \<equiv> \<nu> inp. (inp \<triangleleft> m \<parallel> broadcaster cs inp)"

(* Equivalence proof. *)

lemma broadcaster_system_step: "broadcaster_system (c # cs) m \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> broadcaster_system cs m"
proof -
  have "broadcaster_system (c # cs) m = \<nu> inp. (inp \<triangleleft> m \<parallel> broadcaster (c # cs) inp)"
    using broadcaster_system_def by simp
  also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (\<parallel>a \<leftarrow> (c # cs). a \<triangleleft> x))"
    by (unfold broadcaster_def) simp
  also have "... \<approx>\<^sub>\<sharp> (\<parallel>a \<leftarrow> (c # cs). a \<triangleleft> m)"
    by (blast intro: internal_communication)
  also have "... = c \<triangleleft> m \<parallel> (\<parallel>a \<leftarrow> cs. a \<triangleleft> m)"
    by (unfold big_parallel_def) simp
  also have "... \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (\<parallel>a \<leftarrow> cs. a \<triangleleft> x))"
    using internal_communication and weak_proper_bisim_symmetry and weak_proper_parallel_preservation by fastforce
  also have "... = c \<triangleleft> m \<parallel> \<nu> inp. (inp \<triangleleft> m \<parallel> broadcaster cs inp)"
    by (unfold broadcaster_def) simp
  finally show ?thesis
    using broadcaster_system_def by simp
qed

lemma forwarder_system_step: "forwarder_system (c # cs) m \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> forwarder_system cs m"
proof -
  have "forwarder_system (c # cs) m = \<nu> inp. (inp \<triangleleft> m \<parallel> forwarder_chain (c # cs) inp)"
    using forwarder_system_def by simp
  also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> chain (c # cs) forwarder inp undefined)"
    using forwarder_chain_def by simp
  also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> (forwarder c \<frown> chain cs forwarder) inp undefined)"
    using chain_def by simp
  also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> \<nu> d. (forwarder c inp d \<parallel> chain cs forwarder d undefined))"
    using chaining_op_def by simp
  also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> \<nu> d. (forwarder c inp d \<parallel> forwarder_chain cs d))"
    using forwarder_chain_def by simp
  also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> \<nu> d. (inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d))"
    using forwarder_def by simp
  also have "... \<approx>\<^sub>\<sharp> \<nu> d. (c \<triangleleft> m \<parallel> d \<triangleleft> m \<parallel> forwarder_chain cs d)"
  proof -
    have "\<And>d. \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x)) \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> d \<triangleleft> m"
      using internal_communication by blast
    then have "\<And>d. \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x)) \<approx>\<^sub>\<sharp> \<nu> inp. (c \<triangleleft> m \<parallel> d \<triangleleft> m)"
      using weak_proper_scope_redundancy and weak_proper_bisim_transitivity by blast
    then have "\<And>d. \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x)) \<parallel> forwarder_chain cs d \<approx>\<^sub>\<sharp> \<nu> inp. (c \<triangleleft> m \<parallel> d \<triangleleft> m) \<parallel> forwarder_chain cs d"
      using weak_proper_parallel_preservation by simp
    moreover have "\<And>d. \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x)) \<parallel> forwarder_chain cs d"
      using weak_proper_parallel_scope_extension and weak_proper_bisim_symmetry
      by (meson weak_proper_bisim_transitivity weak_proper_new_channel_preservation weak_proper_parallel_associativity)
    moreover have "\<And>d. \<nu> inp. (c \<triangleleft> m \<parallel> d \<triangleleft> m) \<parallel> forwarder_chain cs d \<approx>\<^sub>\<sharp> \<nu> inp. (c \<triangleleft> m \<parallel> d \<triangleleft> m \<parallel> forwarder_chain cs d)"
      using weak_proper_parallel_scope_extension
      by (meson weak_proper_bisim_transitivity weak_proper_new_channel_preservation weak_proper_parallel_associativity)
    ultimately have "\<And>d. \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> inp. (c \<triangleleft> m \<parallel> d \<triangleleft> m \<parallel> forwarder_chain cs d)"
      using weak_proper_bisim_transitivity by blast
    then have "\<nu> d. \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> d. \<nu> inp. (c \<triangleleft> m \<parallel> d \<triangleleft> m \<parallel> forwarder_chain cs d)"
      using weak_proper_new_channel_preservation by simp
    moreover have "\<nu> inp. (inp \<triangleleft> m \<parallel> \<nu> d. (inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)) \<approx>\<^sub>\<sharp> \<nu> d. \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)"
    proof -
      have "\<And>inp. inp \<triangleleft> m \<parallel> \<nu> d. (inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> d. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)"
        using weak_proper_parallel_scope_redundancy and weak_proper_bisim_symmetry by simp
      then have "\<nu> inp. (inp \<triangleleft> m \<parallel> \<nu> d. (inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)) \<approx>\<^sub>\<sharp> \<nu> inp. \<nu> d. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)"
        using weak_proper_new_channel_preservation by simp
      moreover have "\<nu> inp. \<nu> d. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> d. \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)"
        using weak_proper_new_channel_scope_extension by simp
      ultimately show ?thesis
        using weak_proper_bisim_transitivity by blast
    qed
    moreover have "\<nu> d. \<nu> inp. (c \<triangleleft> m \<parallel> d \<triangleleft> m \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> d. (c \<triangleleft> m \<parallel> d \<triangleleft> m \<parallel> forwarder_chain cs d)"
    proof -
      have "\<And>d. \<nu> inp. (c \<triangleleft> m \<parallel> d \<triangleleft> m \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> d \<triangleleft> m \<parallel> forwarder_chain cs d"
        using weak_proper_scope_redundancy and weak_proper_bisim_symmetry by simp
      then show ?thesis
        using weak_proper_new_channel_preservation by simp
    qed
    ultimately show ?thesis
      using weak_proper_bisim_transitivity by blast
  qed
  also have "... \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> \<nu> d. (d \<triangleleft> m \<parallel> forwarder_chain cs d)"
    using weak_proper_parallel_scope_extension and weak_proper_parallel_scope_redundancy by simp
  also have "... = c \<triangleleft> m \<parallel> forwarder_system cs m"
    using forwarder_system_def by simp
  finally show ?thesis .
qed

theorem equivalence: "forwarder_system cs m \<approx>\<^sub>\<sharp> broadcaster_system cs m"
proof (induction cs)
  case Nil
  then have "forwarder_system [] m = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. \<zero>)"
    using forwarder_system_def and forwarder_chain_def and chain_def by simp
  moreover have "broadcaster_system [] m = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. \<zero>)"
  proof -
    have "broadcaster_system [] m = \<nu> inp. (inp \<triangleleft> m \<parallel> broadcaster [] inp)"
      by (unfold broadcaster_system_def) simp
    also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (\<parallel>c \<leftarrow> []. c \<triangleleft> x))"
      by (unfold broadcaster_def) simp
    also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. \<zero>)"
      by (unfold big_parallel_def) simp
    finally show ?thesis
      by simp
  qed
  ultimately show ?case
    by (simp add: weak_proper_bisim_reflexivity)
next
  case (Cons c cs)
  then have "forwarder_system cs m \<approx>\<^sub>\<sharp> broadcaster_system cs m"
    using Cons.IH by simp
  then have "c \<triangleleft> m \<parallel> forwarder_system cs m \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> broadcaster_system cs m"
    using weak_proper_parallel_preservation by simp
  then have "forwarder_system (c # cs) m \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> broadcaster_system cs m"
    using forwarder_system_step and weak_proper_parallel_preservation and weak_proper_bisim_transitivity by blast 
  then show ?case
    using broadcaster_system_step and weak_proper_parallel_preservation and weak_proper_bisim_transitivity
    by (meson weak_proper_bisim_symmetry)
qed

end
