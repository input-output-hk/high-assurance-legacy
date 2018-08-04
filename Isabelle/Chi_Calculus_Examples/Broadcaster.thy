section \<open>Broadcaster\<close>

text \<open>
  We implement a broadcasting server that forwards incoming values to channels that have been previously
  registered by interested parties.
\<close>

theory Broadcaster
 imports Chi_Calculus.Processes
begin

text \<open>
  We define a special data type for the values that are sent or received along channels.
\<close>

datatype ('a, 'chan) broadcaster_cmd = Reg 'chan | Input 'a

datatype ('a, 'chan) val = 
    Chan 'chan 
  | Val 'a 
  | BrCmd "('a, 'chan) broadcaster_cmd" 
  | Nothing

text \<open>
  We define names to be composed by a tag indicating the process to be invoked plus the required
  arguments for the process.
\<close>

datatype 'chan name = 
    RegCommanderInvoke 'chan 'chan 
  | InputCommanderInvoke 'chan 'chan 
  | BroadcastInvoke "('chan list)" 'chan
  | SenderInvoke nat 'chan
  | ListenerInvoke 'chan

text \<open>
  We define a synonym for the type of the processes that comprise the system.
\<close>

type_synonym ('a, 'chan) br_process = "('chan name, 'chan, ('a, 'chan) val) process"

text \<open>
  The following is the definition of a process which manages incoming registration requests from 
  interested parties and forwards them to the \<open>broadcast\<close> process (defined later).
\<close>

abbreviation reg_commander :: "'chan \<Rightarrow> 'chan \<Rightarrow> ('a, 'chan) br_process"
where
  "reg_commander regs cmds \<equiv> 
    \<cdot>regs \<triangleright> m. (
      case m of Chan reg \<Rightarrow> 
        \<cdot>cmds \<triangleleft> BrCmd (Reg reg) 
        \<parallel> 
        \<langle>RegCommanderInvoke regs cmds\<rangle> Nothing)"

text \<open>
  Also, the following is the definition of a process which manages incoming values from 
  interested parties and forwards them to the \<open>broadcast\<close> process.
\<close>

abbreviation input_commander :: "'chan \<Rightarrow> 'chan \<Rightarrow> ('a, 'chan) br_process"
where
  "input_commander inputs cmds \<equiv> 
    \<cdot>inputs \<triangleright> m. (
      case m of Val val \<Rightarrow> 
        \<cdot>cmds \<triangleleft> BrCmd (Input val) 
        \<parallel> 
        \<langle>InputCommanderInvoke inputs cmds\<rangle> Nothing)"

text \<open>
  Plus, we define a process which keeps the set of channels associated to the parties registered 
  so far, and forwards incoming values to those parties along their associated channels.
\<close>

abbreviation broadcast :: "'chan list \<Rightarrow> 'chan \<Rightarrow> ('a, 'chan) br_process"
where
  "broadcast chans cmds \<equiv> 
    \<cdot>cmds \<triangleright> m. (
      case m of
        BrCmd (Reg chan)  \<Rightarrow> \<langle>BroadcastInvoke (chan # chans) cmds\<rangle> Nothing |
        BrCmd (Input val) \<Rightarrow> foldr (\<lambda> chan p. \<cdot>chan \<triangleleft> Val val \<parallel> p) chans \<zero>)"

text \<open>
  Now, given the three processes defined above, we assemble them into the broadcasting server 
  process.
\<close>

abbreviation broadcaster :: "'chan \<Rightarrow> 'chan \<Rightarrow> ('a, 'chan) br_process"
where 
  "broadcaster regs inputs \<equiv> \<nu> cmds. (
    reg_commander regs cmds
    \<parallel>
    input_commander inputs cmds
    \<parallel>
    broadcast [] cmds)"

text \<open>
  Finally, we define a system comprised by the broadcasting server, two client processes which
  receive the broadcast values, and a client process which broadcasts a sequence of natural numbers.
\<close>

abbreviation sender :: "nat \<Rightarrow> 'chan \<Rightarrow> (nat, 'chan) br_process"
where
  "sender n inputs \<equiv> \<cdot>inputs \<triangleleft> Val n \<parallel> \<langle>SenderInvoke (Suc n) inputs\<rangle> Nothing"

abbreviation listener :: "'chan \<Rightarrow> (nat, 'chan) br_process"
where
  "listener brinp \<equiv> \<cdot>brinp \<triangleright> val. \<langle>ListenerInvoke brinp\<rangle> Nothing"

abbreviation receiver :: "'chan \<Rightarrow> (nat, 'chan) br_process"
where
  "receiver regs \<equiv> \<nu> brinp.(\<cdot>regs \<triangleleft> Chan brinp \<parallel> listener brinp)"

abbreviation system :: "(nat, 'chan) br_process"
where
  "system \<equiv> \<nu> regs inputs. (
    broadcaster regs inputs
    \<parallel>
    receiver regs
    \<parallel> 
    receiver regs
    \<parallel>
    sender 0 inputs)"

end
