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

(* Chaining operator. *)

abbreviation
  chaining_op :: "[[chan, chan] \<Rightarrow> process, [chan, chan] \<Rightarrow> process] \<Rightarrow> ([chan, chan] \<Rightarrow> process)" (infixr "\<frown>" 60)
where
  "chaining_op P Q \<equiv> \<lambda>inp out. \<nu> c. (P inp c \<parallel> Q c out)"

(* TODO: Prove it. *)
lemma chaining_op_associativity: "(P \<frown> Q) \<frown> R = P \<frown> (Q \<frown> R)"
  sorry

(* Forwarder process. *)

definition
  forwarder :: "[chan, chan] \<Rightarrow> process"
where
  "forwarder inp out \<equiv> inp \<triangleright> x. out \<triangleleft> x"

(* TODO: Prove it. *)
lemma prepend_forwarder_is_forwarder:
  "P inp out \<approx>\<^sub>\<flat> forwarder inp out \<Longrightarrow> (forwarder \<frown> P) inp out \<approx>\<^sub>\<flat> forwarder inp out"
  sorry

abbreviation
  chain :: "[nat, [chan, chan] \<Rightarrow> process] \<Rightarrow> ([chan, chan] \<Rightarrow> process)"
where
  "chain n P \<equiv> foldr (\<frown>) (replicate n P) P"

lemma forwarder_chain_is_forwarder: "chain n forwarder inp out \<approx>\<^sub>\<flat> forwarder inp out"
proof (induction n)
  case 0
  then have "chain 0 forwarder = forwarder"
    by simp
  then show ?case
    by (simp add: weak_basic_bisim_reflexivity)
next
  case (Suc n)
  let ?fs = "replicate n forwarder"
  have "replicate (Suc n) forwarder = forwarder # ?fs"
    by simp
  then have "foldr (\<frown>) (forwarder # ?fs) forwarder = forwarder \<frown> foldr (\<frown>) ?fs forwarder"
    by simp
  moreover have "(foldr (\<frown>) ?fs forwarder) inp out \<approx>\<^sub>\<flat> forwarder inp out"
    using Suc.IH by simp
  ultimately show ?case
    using prepend_forwarder_is_forwarder by simp
qed

end
