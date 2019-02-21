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

text \<open>
  The following is the proof that broadcast is observationally equivalent to a tree of forwarders.
\<close>

(* Rose trees. *)

datatype 'a tree = Node (tval: 'a) (children: "'a tree list")

fun
  tree_as_list :: "'a tree \<Rightarrow> 'a list"
where
  "tree_as_list (Node x []) = [x]"
| "tree_as_list (Node x ts) = x # List.bind ts tree_as_list"

abbreviation
  tree_as_set :: "'a tree \<Rightarrow> 'a set"
where
  "tree_as_set \<equiv> set o tree_as_list"

abbreviation
  size :: "'a tree \<Rightarrow> nat"
where
  "size \<equiv> length o tree_as_list"

abbreviation
  leaf :: "'a \<Rightarrow> 'a tree"
where
  "leaf x \<equiv> Node x []"

abbreviation
  is_leaf :: "'a tree \<Rightarrow> bool"
where
  "is_leaf t \<equiv> \<exists>x. t = leaf x"

lemma tree_size: "size (Node x ts) = 1 + (\<Sum>t\<leftarrow>ts. size t)"
proof -
  have "size (Node x ts) = length (tree_as_list (Node x ts))"
    by simp
  also have "... = length (x # List.bind ts tree_as_list)"
    by (metis List.bind_def concat.simps(1) list.exhaust list.simps(8) tree_as_list.simps)
  also have "... = 1 + length (List.bind ts tree_as_list)"
    by simp
  also have "... = 1 + length (concat (map tree_as_list ts))"
    by (unfold List.bind_def) simp
  also have "... = 1 + sum_list (map length (map tree_as_list ts))"
    by (simp add: length_concat)
  also have "... = 1 + sum_list (map (length o tree_as_list) ts)"
    by simp
  finally show ?thesis
    by blast
qed

lemma tree_child_size:
  assumes "ts \<noteq> []"
  and "i \<in> {0..< length ts}"
  shows "size (ts ! i) < size (Node x ts)"
  using assms
proof -
  assume "ts \<noteq> []" and "i \<in> {0..< length ts}"
  then have "size (ts ! i) \<le> (\<Sum>t\<leftarrow>ts. size t)"
    by (metis atLeastLessThan_iff elem_le_sum_list length_map nth_map)
  moreover have "size (Node x ts) = 1 + (\<Sum>t\<leftarrow>ts. size t)"
    using tree_size by simp
  ultimately show ?thesis
    by linarith
qed

lemma tree_partition: "tree_as_list tp = tval tp # List.bind (children tp) tree_as_list"
proof -
  obtain x and ts where "tp = Node x ts"
    by (rule tree.exhaust_sel)
  then show ?thesis
  proof (cases ts)
    case Nil
    have "tree_as_list tp = [x]"
      by (simp add: tree_as_list.simps(1) \<open>tp = Node x ts\<close> \<open>ts = []\<close>)
    also have "... = x # List.bind [] tree_as_list"
      unfolding bind_simps(1) by simp
    finally show ?thesis
      by (simp add: \<open>tp = Node x ts\<close> \<open>ts = []\<close>)
  next
    case (Cons t ts')
    have "tree_as_list tp = x # List.bind ts tree_as_list"
      by (simp add: tree_as_list.simps(2) \<open>tp = Node x ts\<close> \<open>ts = t # ts'\<close>)
    then show ?thesis
      by (simp add: \<open>tp = Node x ts\<close>)
  qed
qed

lemma tree_as_list_map: "children tp \<noteq> [] \<Longrightarrow> (\<And>i. i \<in> {0..< length (children tp)} \<Longrightarrow> tree_as_list (children tp ! i) = map tree_as_list (children tp) ! i)"
  by simp

(* Tree topology. It's implemented simply as a tree of channels. This set of channels is comprised
   by the channels used by forwarders to deliver the broadcast message to the receiving processes. *)

type_synonym tree_topology = "chan tree"

(* Generator of a tree of forwarders from a given tree topology. Each forwarder is actually implemented
   as a broadcaster. *)

function
  tree_forwarder :: "[chan, tree_topology] \<Rightarrow> process"
where
  "tree_forwarder inp (Node dlv ts) = (
    if ts = []
    then
      broadcaster [dlv] inp
    else
      restrict
        (length ts)
        (\<lambda>inpps.
          broadcaster (dlv # inpps) inp
          \<parallel>
          (\<parallel>i \<leftarrow> [0..< length ts]. tree_forwarder (inpps ! i) (ts ! i))))"
by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, t). size t)", auto)
  using tree_child_size by fastforce+

(**
  Examples:

    tree_topology_1: dlv1

    tree_topology_2: dlv1
                      |__ dlv2

    tree_topology_3: dlv1
                      |__ dlv2
                      |__ dlv3

    tree_topology_4: dlv1
                      |__ dlv2
                           |__ dlv3
**)

context
  fixes dlv1 dlv2 dlv3 :: chan
begin

abbreviation
  tree_topology_1
where
  "tree_topology_1 \<equiv> leaf dlv1"

abbreviation
  tree_topology_2
where
  "tree_topology_2 \<equiv> Node dlv1 [leaf dlv2]"

abbreviation
  tree_topology_3
where
  "tree_topology_3 \<equiv> Node dlv1 [leaf dlv2, leaf dlv3]"

abbreviation
  tree_topology_4
where
  "tree_topology_4 \<equiv> Node dlv1 [Node dlv2 [leaf dlv3]]"

(* inp \<triangleright> m. (dlv1 \<triangleleft> m \<parallel> \<zero>) *)
value "tree_forwarder inp tree_topology_1"

(* \<nu> inp1. (inp \<triangleright> m. (dlv1 \<triangleleft> m \<parallel> inp1 \<triangleleft> m \<parallel> \<zero>) \<parallel> inp1 \<triangleright> m. (dlv2 \<triangleleft> m \<parallel> \<zero>) \<parallel> \<zero>) *)
value "tree_forwarder inp tree_topology_2"

(* \<nu> inp1 inp2. (inp \<triangleright> m. (dlv1 \<triangleleft> m \<parallel> inp1 \<triangleleft> m \<parallel> inp2 \<triangleleft> m \<parallel> \<zero>) \<parallel> inp1 \<triangleright> m. (dlv2 \<triangleleft> m \<parallel> \<zero>) \<parallel> inp2 \<triangleright> m. (dlv3 \<triangleleft> m \<parallel> \<zero>) \<parallel> \<zero>) *)
value "tree_forwarder inp tree_topology_3"

(* \<nu> inp1. (inp \<triangleright> m. (dlv1 \<triangleleft> m \<parallel> inp1 \<triangleleft> m \<parallel> \<zero>) \<parallel> \<nu> inp2. (inp1 \<triangleright> m. (dlv2 \<triangleleft> m \<parallel> inp2 \<triangleleft> m \<parallel> \<zero>) \<parallel> inp2 \<triangleright> m. (dlv3 \<triangleleft> m \<parallel> \<zero>) \<parallel> \<zero>) \<parallel> \<zero>) *)
value "tree_forwarder inp tree_topology_4"

lemma "tree_forwarder inp tree_topology_1 = broadcaster [dlv1] inp"
  by simp

lemma "tree_forwarder inp tree_topology_2 = \<nu> inp2. (broadcaster [dlv1, inp2] inp \<parallel> broadcaster [dlv2] inp2 \<parallel> \<zero>)"
proof -
  let ?ts = "[leaf dlv2]"
  have "tree_forwarder inp tree_topology_2 =
    restrict
      (length ?ts)
      (\<lambda>inpps. broadcaster (dlv1 # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< length ?ts]. tree_forwarder (inpps ! i) (?ts ! i)))"
    unfolding tree_forwarder.simps by simp
  also have "... =
    restrict
      (Suc 0)
      (\<lambda>inpps. broadcaster (dlv1 # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< Suc 0]. tree_forwarder (inpps ! i) (?ts ! i)))"
    by simp
  also have "... =
    restrict
      (Suc 0)
      (\<lambda>inpps. broadcaster (dlv1 # inpps) inp \<parallel> tree_forwarder (inpps ! 0) (?ts ! 0) \<parallel> \<zero>)"
    by (unfold big_parallel_def) simp
  also have "... = \<nu> inp2. (broadcaster (dlv1 # [inp2]) inp \<parallel> tree_forwarder ([inp2] ! 0) (?ts ! 0) \<parallel> \<zero>)"
    unfolding restrict.simps by simp
  also have "... = \<nu> inp2. (broadcaster ([dlv1, inp2]) inp \<parallel> tree_forwarder inp2 (leaf dlv2) \<parallel> \<zero>)"
    by simp
  also have "... = \<nu> inp2. (broadcaster ([dlv1, inp2]) inp \<parallel> broadcaster [dlv2] inp2 \<parallel> \<zero>)"
    unfolding tree_forwarder.simps by simp
  finally show ?thesis
    by simp
qed

lemma "tree_forwarder inp tree_topology_3 =
  \<nu> inp2 inp3. (broadcaster [dlv1, inp2, inp3] inp \<parallel> broadcaster [dlv2] inp2 \<parallel> broadcaster [dlv3] inp3 \<parallel> \<zero>)"
proof -
  let ?ts = "[leaf dlv2, leaf dlv3]"
  have "tree_forwarder inp tree_topology_3 =
    restrict
      (length ?ts)
      (\<lambda>inpps. broadcaster (dlv1 # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< length ?ts]. tree_forwarder (inpps ! i) (?ts ! i)))"
    unfolding tree_forwarder.simps by simp
  also have "... =
    restrict
      (Suc (Suc 0))
      (\<lambda>inpps. broadcaster (dlv1 # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< Suc (Suc 0)]. tree_forwarder (inpps ! i) (?ts ! i)))"
    by simp
  also have "... = \<nu> inp2 inp3. (broadcaster (dlv1 # [inp2, inp3]) inp \<parallel> (\<parallel>i \<leftarrow> [0..< Suc (Suc 0)]. tree_forwarder ([inp2, inp3] ! i) (?ts ! i)))"
    unfolding restrict.simps by simp
  also have "... = \<nu> inp2 inp3. (broadcaster [dlv1, inp2, inp3] inp \<parallel> tree_forwarder inp2 (Node dlv2 []) \<parallel> tree_forwarder inp3 (leaf dlv3) \<parallel> \<zero>)"
    by (unfold big_parallel_def) simp
  also have "... = \<nu> inp2 inp3. (broadcaster [dlv1, inp2, inp3] inp \<parallel> broadcaster [dlv2] inp2 \<parallel> broadcaster [dlv3] inp3 \<parallel> \<zero>)"
    unfolding tree_forwarder.simps by simp
  finally show ?thesis
    by simp
qed

lemma "tree_forwarder inp tree_topology_4 =
  \<nu> inp2. (broadcaster [dlv1, inp2] inp \<parallel> \<nu> inp3. (broadcaster [dlv2, inp3] inp2 \<parallel> broadcaster [dlv3] inp3 \<parallel> \<zero>) \<parallel> \<zero>)"
proof -
  let ?ts2 = "[leaf dlv3]"
  let ?ts1 = "[Node dlv2 ?ts2]"
  have "tree_forwarder inp tree_topology_4 =
    restrict
      (length ?ts1)
      (\<lambda>inpps. broadcaster (dlv1 # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< length ?ts1]. tree_forwarder (inpps ! i) (?ts1 ! i)))"
    unfolding tree_forwarder.simps by simp
  also have "... =
    restrict
      (Suc 0)
      (\<lambda>inpps. broadcaster (dlv1 # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< Suc 0]. tree_forwarder (inpps ! i) (?ts1 ! i)))"
    by simp
  also have "... = \<nu> inp2. (broadcaster (dlv1 # [inp2]) inp \<parallel> (\<parallel>i \<leftarrow> [0..< Suc 0]. tree_forwarder ([inp2] ! i) (?ts1 ! i)))"
    unfolding restrict.simps by simp
  also have "... = \<nu> inp2. (broadcaster (dlv1 # [inp2]) inp \<parallel> tree_forwarder ([inp2] ! 0) (?ts1 ! 0) \<parallel> \<zero>)"
    by (unfold big_parallel_def) simp
  also have "... = \<nu> inp2. (broadcaster [dlv1, inp2] inp \<parallel> tree_forwarder inp2 (Node dlv2 ?ts2) \<parallel> \<zero>)"
    by simp
  also have "... = \<nu> inp2. (broadcaster [dlv1, inp2] inp
    \<parallel> restrict
        (length ?ts2)
        (\<lambda>inpps. broadcaster (dlv2 # inpps) inp2 \<parallel> (\<parallel>i \<leftarrow> [0..< length [Node dlv3 []]]. tree_forwarder (inpps ! i) (?ts2 ! i)))
    \<parallel> \<zero>)"
    unfolding tree_forwarder.simps by simp
  also have "... = \<nu> inp2. (broadcaster [dlv1, inp2] inp
    \<parallel> restrict
        (Suc 0)
        (\<lambda>inpps. broadcaster (dlv2 # inpps) inp2 \<parallel> (\<parallel>i \<leftarrow> [0..< Suc 0]. tree_forwarder (inpps ! i) (?ts2 ! i)))
    \<parallel> \<zero>)"
    by simp
  also have "... = \<nu> inp2. (broadcaster [dlv1, inp2] inp
    \<parallel> \<nu> inp3. (broadcaster (dlv2 # [inp3]) inp2 \<parallel> (\<parallel>i \<leftarrow> [0..< Suc 0]. tree_forwarder ([inp3] ! i) (?ts2 ! i)))
    \<parallel> \<zero>)"
    unfolding restrict.simps by simp
  also have "... = \<nu> inp2. (broadcaster [dlv1, inp2] inp \<parallel> \<nu> inp3. (broadcaster [dlv2, inp3] inp2 \<parallel> tree_forwarder inp3 (leaf dlv3) \<parallel> \<zero>) \<parallel> \<zero>)"
    by (unfold big_parallel_def) simp
  also have "... = \<nu> inp2. (broadcaster [dlv1, inp2] inp \<parallel> \<nu> inp3. (broadcaster [dlv2, inp3] inp2 \<parallel> broadcaster [dlv3] inp3 \<parallel> \<zero>) \<parallel> \<zero>)"
    unfolding tree_forwarder.simps by simp
  finally show ?thesis
    by simp
qed

definition
  tree_forwarder_system :: "[tree_topology, val] \<Rightarrow> process"
where
  "tree_forwarder_system topology m \<equiv> \<nu> inp. (inp \<triangleleft> m \<parallel> tree_forwarder inp topology)"

(** Equivalence proof. **)

lemma tree_forwarder_subtrees_collapse:
  assumes "tp = Node dlv ts"
  and "n = length ts"
  and "ts \<noteq> []"
  and "\<And>inpps i. i \<in> {0..< n} \<Longrightarrow> tree_forwarder (inpps ! i) (ts ! i) \<approx>\<^sub>\<sharp> broadcaster (tree_as_list (ts ! i)) (inpps ! i)"
  shows "tree_forwarder inp tp \<approx>\<^sub>\<sharp>
    restrict
      n
      (\<lambda>inpps.
        broadcaster (dlv # inpps) inp
        \<parallel>
        (\<parallel>i \<leftarrow> [0..< n]. broadcaster (tree_as_list (ts ! i)) (inpps ! i)))"
  using assms
proof -
  have "\<And>inpps. (\<parallel>i \<leftarrow> [0..< n]. tree_forwarder (inpps ! i) (ts ! i)) \<approx>\<^sub>\<sharp> (\<parallel>i \<leftarrow> [0..< n]. broadcaster (tree_as_list (ts ! i)) (inpps ! i))"
    using weak_proper_indexed_big_parallel_preservation by (simp add: assms(2-4))
  then have "\<And>inpps.
    broadcaster (dlv # inpps) inp  \<parallel> (\<parallel>i \<leftarrow> [0..< n]. tree_forwarder (inpps ! i) (ts ! i))
    \<approx>\<^sub>\<sharp>
    broadcaster (dlv # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< n]. broadcaster (tree_as_list (ts ! i)) (inpps ! i))"
    using weak_proper_parallel_preservation by simp
  then have "\<And>inpps.
    restrict n (\<lambda>inpps. broadcaster (dlv # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< n]. tree_forwarder (inpps ! i) (ts ! i)))
    \<approx>\<^sub>\<sharp>
    restrict n (\<lambda>inpps. broadcaster (dlv # inpps) inp \<parallel> (\<parallel>i \<leftarrow> [0..< n]. broadcaster (tree_as_list (ts ! i)) (inpps ! i)))"
    using weak_proper_restrict_preservation by simp
  then show ?thesis
    by (simp add: assms(1-3))
qed

lemma broadcaster_children_absorb:
  assumes "dlvs \<noteq> []"
  and "length dlvs = n"
  shows
    "restrict
      n
      (\<lambda>inpps.
        broadcaster (dlv # inpps) inp
        \<parallel>
        (\<parallel>i \<leftarrow> [0..< n]. broadcaster (dlvs ! i) (inpps ! i)))
    \<approx>\<^sub>\<sharp>
    broadcaster (dlv # concat dlvs) inp"
sorry

lemma broadcast_tree_forwarder_equivalence_aux: "tree_forwarder inp tp \<approx>\<^sub>\<sharp> broadcaster (tree_as_list tp) inp"
proof (induction "size tp" arbitrary: tp inp rule: less_induct)
  case (less tp)
  then show ?case
  proof (cases "is_leaf tp")
    case True
    obtain dlv where "tp = leaf dlv"
      using True by blast
    then have "tree_as_list tp = [dlv]"
      by (blast intro: tree_as_list.simps(1))
    also have "tree_forwarder inp tp = broadcaster [dlv] inp"
      by (simp add: \<open>tp = leaf dlv\<close>)
    finally show ?thesis
      by (simp add: weak_proper_bisim_reflexivity \<open>tree_as_list tp = [dlv]\<close>)
  next
    case False
    let ?fts = "children tp"
    let ?n = "length ?fts"
    have "?fts \<noteq> []"
      by (metis False tree.collapse)
    then have "\<forall>i \<in> {0..< ?n}. size (?fts ! i) < size tp"
      by (metis tree_child_size tree.collapse)
    then have "\<And>inpps i. i \<in> {0..< ?n} \<Longrightarrow> tree_forwarder (inpps ! i) (?fts ! i) \<approx>\<^sub>\<sharp> broadcaster (tree_as_list (?fts ! i)) (inpps ! i)"
      by (blast intro: less.hyps)
    then have "tree_forwarder inp tp \<approx>\<^sub>\<sharp>
      restrict ?n (\<lambda>inpps. broadcaster (tval tp # inpps) inp
        \<parallel> (\<parallel>i \<leftarrow> [0..< ?n]. broadcaster (tree_as_list (?fts ! i)) (inpps ! i)))"
      using tree_forwarder_subtrees_collapse by (meson \<open>?fts \<noteq> []\<close> tree.exhaust_sel)
    also have "... \<approx>\<^sub>\<sharp> broadcaster (tval tp # (List.bind ?fts tree_as_list)) inp"
      using broadcaster_children_absorb and tree_as_list_map
      (* FIXME: Find a nicer proof. *)
      by (smt List.bind_def \<open>children tp \<noteq> []\<close> length_greater_0_conv length_map weak_proper_bisim_reflexivity weak_proper_bisim_transitivity weak_proper_indexed_big_parallel_preservation weak_proper_parallel_preservation(2) weak_proper_restrict_preservation)
    finally show ?thesis
      by (simp add: tree_partition)
  qed
qed

theorem broadcast_tree_forwarder_equivalence: "tree_forwarder_system tp m \<approx>\<^sub>\<sharp> broadcaster_system (tree_as_list tp) m"
proof -
  have "\<And>inp. tree_forwarder inp tp \<approx>\<^sub>\<sharp> broadcaster (tree_as_list tp) inp"
    by (fact broadcast_tree_forwarder_equivalence_aux)
  then have "\<And>inp. inp \<triangleleft> m \<parallel> tree_forwarder inp tp \<approx>\<^sub>\<sharp> inp \<triangleleft> m \<parallel> broadcaster (tree_as_list tp) inp"
    by (rule weak_proper_parallel_preservation(2))
  then have "\<nu> inp. (inp \<triangleleft> m \<parallel> tree_forwarder inp tp) \<approx>\<^sub>\<sharp> \<nu> inp. (inp \<triangleleft> m \<parallel> broadcaster (tree_as_list tp) inp)"
    by (fact weak_proper_new_channel_preservation)
  then show ?thesis
    by (unfold broadcaster_system_def tree_forwarder_system_def) simp
qed

end

end
