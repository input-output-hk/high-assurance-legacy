section \<open>Broadcaster\<close>

text \<open>
  We implement a broadcasting server that forwards incoming values to channels that have been previously
  registered by interested parties.
\<close>

theory Broadcaster
  imports
    Chi_Calculus.Typed_Processes
    Chi_Calculus.Proper_Weak_Bisimulation
    "HOL-Library.BNF_Corec"
begin

text \<open>
  We define a special data type for the values that are sent or received along channels.
\<close>

datatype 'a broadcaster_cmd = Reg "'a channel" | Input 'a

instantiation broadcaster_cmd :: (countable) countable
begin
instance by countable_datatype
end

text \<open>
  We define names to be composed by a tag indicating the process to be invoked plus the required
  arguments for the process.
\<close>

text \<open>
  We define a synonym for the type of the processes that comprise the system.
\<close>

text \<open>
  The following is the definition of a process which manages incoming registration requests from 
  interested parties and forwards them to the \<open>broadcast\<close> process (defined later).
\<close>

primcorec reg_commander :: "'a::countable channel channel \<Rightarrow> 'a broadcaster_cmd channel \<Rightarrow> process"
where
  "reg_commander regs cmds =
    regs \<triangleright>\<degree> reg. 
        cmds \<triangleleft>\<degree> Reg reg
        \<parallel> 
        reg_commander regs cmds"

text \<open>
  Also, the following is the definition of a process which manages incoming values from 
  interested parties and forwards them to the \<open>broadcast\<close> process.
\<close>

primcorec input_commander :: "'a::countable channel \<Rightarrow> 'a broadcaster_cmd channel \<Rightarrow> process"
where
  "input_commander inputs cmds =
    inputs \<triangleright>\<degree> val.
        cmds \<triangleleft>\<degree> Input val
        \<parallel> 
        input_commander inputs cmds"

text \<open>
  Plus, we define a process which keeps the set of channels associated to the parties registered 
  so far, and forwards incoming values to those parties along their associated channels.
\<close>

corec
  broadcast :: "'a::countable channel list \<Rightarrow> 'a broadcaster_cmd channel \<Rightarrow> process"
where
  "broadcast chans cmds =
    cmds \<triangleright>\<degree> cmd. (
      (\<exists>chan. cmd = Reg chan) ? (let chan = THE chan. cmd = Reg chan in
        broadcast (chan # chans) cmds
      )
      \<parallel>
      (\<exists>val. cmd = Input val) ? (let val = THE val. cmd = Input val in
        foldr (\<lambda> chan p. chan \<triangleleft>\<degree> val \<parallel> p) chans \<zero>
        \<parallel>
        broadcast chans cmds
      )
    )"

text \<open>
  Now, given the three processes defined above, we assemble them into the broadcasting server 
  process.
\<close>

abbreviation broadcaster :: "'a::countable channel channel \<Rightarrow> 'a channel \<Rightarrow> process"
where 
  "broadcaster regs inputs \<equiv> \<nu>\<degree>cmds. (
    reg_commander regs cmds
    \<parallel>
    input_commander inputs cmds
    \<parallel>
    broadcast [] cmds)"

text \<open>
  Finally, we define a system comprised by the broadcasting server, two client processes which
  receive the broadcast values, and a client process which broadcasts a sequence of natural numbers.
\<close>

primcorec sender :: "nat \<Rightarrow> nat channel \<Rightarrow> process"
where
  "sender n inputs = inputs \<triangleleft>\<degree> n \<parallel> sender (Suc n) inputs"

primcorec listener :: "nat channel \<Rightarrow> process"
where
  "listener brinp = brinp \<triangleright>\<degree> val. listener brinp"

abbreviation receiver :: "nat channel channel \<Rightarrow> process"
where
  "receiver regs \<equiv> \<nu>\<degree>brinp.(regs \<triangleleft>\<degree> brinp \<parallel> listener brinp)"

abbreviation system :: process
where
  "system \<equiv> \<nu>\<degree>regs inputs. (
    broadcaster regs inputs
    \<parallel>
    receiver regs
    \<parallel> 
    receiver regs
    \<parallel>
    sender 0 inputs)"

text \<open>
  The following is the proof that the broadcasting process is observationally equivalent to a
  process in which messages are forwarded to peers.
\<close>

(* General properties. *)
(* TODO: Move this lemmas to a more appropriate file from where they can be re-used. *)

(* TODO: Prove it. *)
lemma internal_communication: "\<nu> c. (c \<triangleleft> y \<parallel> c \<triangleright> x. P x) \<approx>\<^sub>\<sharp> \<nu> c. P y"
  sorry

lemma weak_proper_parallel_scope_redundancy: "\<nu> c. (p \<parallel> P c) \<approx>\<^sub>\<sharp> p \<parallel> \<nu> c. P c"
  (* FIXME: Find a nicer proof. *)
  by (smt
      weak_proper_scope_redundancy
      weak_proper_bisim_elim2
      weak_proper_bisim_transitivity
      weak_proper_new_channel_preservation
      weak_proper_parallel_commutativity
      weak_proper_parallel_scope_extension)

(* Chaining operator. *)

definition
  chaining_op :: "[[chan, chan] \<Rightarrow> process, [chan, chan] \<Rightarrow> process] \<Rightarrow> ([chan, chan] \<Rightarrow> process)" (infixr "\<frown>" 60)
where
  "chaining_op P Q \<equiv> \<lambda>inp out. \<nu> c. (P inp c \<parallel> Q c out)"

(* TODO: Prove it. *)
lemma chaining_op_associativity: "(P \<frown> Q) \<frown> R = P \<frown> (Q \<frown> R)"
  sorry

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

abbreviation
  broadcaster\<^sub>2 :: "[chan list, val] \<Rightarrow> process"
where
  "broadcaster\<^sub>2 cs x \<equiv> foldr (\<lambda>c p. c \<triangleleft> x \<parallel> p) cs \<zero>"

definition
  broadcaster\<^sub>1 :: "[chan list, chan] \<Rightarrow> process"
where
  "broadcaster\<^sub>1 cs inp \<equiv> inp \<triangleright> x. broadcaster\<^sub>2 cs x"

(* Broadcaster system, namely a broadcaster process and a sender process. *)

definition
  broadcaster_system :: "[chan list, val] \<Rightarrow> process"
where
  "broadcaster_system cs m \<equiv> \<nu> inp. (inp \<triangleleft> m \<parallel> broadcaster\<^sub>1 cs inp)"

(* Equivalence proof. *)

lemma broadcaster_system_step: "broadcaster_system (c # cs) m \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> broadcaster_system cs m"
proof -
  have "broadcaster_system (c # cs) m = \<nu> inp. (inp \<triangleleft> m \<parallel> broadcaster\<^sub>1 (c # cs) inp)"
    using broadcaster_system_def by simp
  also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. broadcaster\<^sub>2 (c # cs) x)"
    using broadcaster\<^sub>1_def by simp
  also have "... \<approx>\<^sub>\<sharp> \<nu> inp. broadcaster\<^sub>2 (c # cs) m"
    using internal_communication by simp
  also have "... = \<nu> inp. (c \<triangleleft> m \<parallel> broadcaster\<^sub>2 cs m)"
    by simp
  also have "... \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> \<nu> inp. broadcaster\<^sub>2 cs m"
    using weak_proper_parallel_scope_redundancy by simp
  also have "... \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. broadcaster\<^sub>2 cs x)"
    using internal_communication and weak_proper_bisim_symmetry and weak_proper_parallel_preservation by fastforce
  also have "... = c \<triangleleft> m \<parallel> \<nu> inp. (inp \<triangleleft> m \<parallel> broadcaster\<^sub>1 cs inp)"
    using broadcaster\<^sub>1_def by simp
  finally show ?thesis
    using broadcaster_system_def by simp
qed

(* TODO: Prove it. *)
lemma aux1: "\<nu> d. (inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> inp \<triangleright> x. \<nu> d. ((c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)"
  sorry

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
  also have "... \<approx>\<^sub>\<sharp> \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. \<nu> d. ((c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d))"
  proof -
    have "\<And>inp. \<nu> d. (inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> inp \<triangleright> x. \<nu> d. ((c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)"
      using aux1 by simp
    then have "\<And>inp. inp \<triangleleft> m \<parallel> \<nu> d. ((inp \<triangleright> x. (c \<triangleleft> x \<parallel> d \<triangleleft> x)) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> inp \<triangleleft> m \<parallel> inp \<triangleright> x. (\<nu> d. ((c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d))"
      using weak_proper_parallel_preservation by simp
    then show ?thesis
      using weak_proper_new_channel_preservation by simp
  qed
  also have "... \<approx>\<^sub>\<sharp> \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> \<nu> d. (d \<triangleleft> x \<parallel> forwarder_chain cs d)))"
  proof -
    have 1: "\<And>x. \<nu> d. ((c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> d. (c \<triangleleft> x \<parallel> (d \<triangleleft> x \<parallel> forwarder_chain cs d))"
      using weak_proper_parallel_associativity and weak_proper_new_channel_preservation by simp
    then have "\<And>x. c \<triangleleft> x \<parallel> \<nu> d. (d \<triangleleft> x \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> d. (c \<triangleleft> x \<parallel> (d \<triangleleft> x \<parallel> forwarder_chain cs d))"
      using weak_proper_parallel_scope_redundancy and weak_proper_bisim_symmetry by simp
    then have "\<And>x. c \<triangleleft> x \<parallel> \<nu> d. (d \<triangleleft> x \<parallel> forwarder_chain cs d) \<approx>\<^sub>\<sharp> \<nu> d. ((c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d)"
      using 1 and weak_proper_bisim_symmetry and weak_proper_bisim_transitivity by smt
    then have "\<And>inp. inp \<triangleright> x. (c \<triangleleft> x \<parallel> \<nu> d. (d \<triangleleft> x \<parallel> forwarder_chain cs d)) \<approx>\<^sub>\<sharp> inp \<triangleright> x. (\<nu> d. ((c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d))"
      using weak_proper_receive_preservation by simp
    then have "\<And>inp. inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> \<nu> d. (d \<triangleleft> x \<parallel> forwarder_chain cs d)) \<approx>\<^sub>\<sharp> inp \<triangleleft> m \<parallel> inp \<triangleright> x. (\<nu> d. ((c \<triangleleft> x \<parallel> d \<triangleleft> x) \<parallel> forwarder_chain cs d))"
      using weak_proper_parallel_preservation by simp
    then show ?thesis
      using weak_proper_new_channel_preservation and weak_proper_bisim_symmetry by simp
  qed
  also have "... = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. (c \<triangleleft> x \<parallel> forwarder_system cs x))"
    using forwarder_system_def by simp
  also have "... \<approx>\<^sub>\<sharp> \<nu> inp. (c \<triangleleft> m \<parallel> forwarder_system cs m)"
    using internal_communication by blast
  also have "... \<approx>\<^sub>\<sharp> c \<triangleleft> m \<parallel> forwarder_system cs m"
    using weak_proper_scope_redundancy and weak_proper_bisim_symmetry by simp
  finally show ?thesis .
qed

theorem equivalence: "forwarder_system cs m \<approx>\<^sub>\<sharp> broadcaster_system cs m"
proof (induction cs)
  case Nil
  then have "forwarder_system [] m = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. \<zero>)"
    using forwarder_system_def and forwarder_chain_def and chain_def by simp
  moreover have "broadcaster_system [] m = \<nu> inp. (inp \<triangleleft> m \<parallel> inp \<triangleright> x. \<zero>)"
    using broadcaster_system_def and broadcaster\<^sub>1_def by simp
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
