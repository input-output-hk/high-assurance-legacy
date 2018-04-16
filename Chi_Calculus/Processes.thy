section \<open>Processes\<close>

theory Processes
  imports Main
begin

text \<open>
  The definition of the type of processes is fairly straightforward.
\<close>

datatype ('name, 'chan, 'val) process =
  Stop ("\<zero>") |
  UnicastInput 'chan "('val \<Rightarrow> ('name, 'chan, 'val) process)" |
  UnicastOutput 'chan 'val (infixr "\<triangleleft>" 100) |
  BroadcastInput "('val \<Rightarrow> ('name, 'chan, 'val) process)" |
  BroadcastOutput 'val ("\<star> \<triangleleft> _" [100] 100) |
  Parallel "(('name, 'chan, 'val) process)" "(('name, 'chan, 'val) process)" (infixr "\<parallel>" 65) |
  NewChannel "('chan \<Rightarrow> ('name, 'chan, 'val) process)" (binder "\<nu>" 100) |
  Invoke 'name 'val ("\<langle>_\<rangle> _" [0, 100] 100)

(*
  It might be good to never use a concrete channel type and introduce global channels by passing
  them as function arguments.
*)

text \<open>
  The notations for \<^const>\<open>UnicastInput\<close> and \<^const>\<open>BroadcastInput\<close> cannot be declared with
  \<^bold>\<open>binder\<close>, for the following reasons:

    \<^item> They do not allow binding multiple variables in one go (like in \<open>\<forall>x\<^sub>1 \<dots> x\<^sub>n. [\<dots>]\<close>).

    \<^item> The notation for \<^const>\<open>UnicastInput\<close> has an extra parameter (for the channel) before the
      binder.

  Therefore we introduce these notations using the low-level \<^bold>\<open>syntax\<close> and \<^bold>\<open>translations\<close>
  constructs.
\<close>

syntax
  "_UnicastInput" :: "'chan \<Rightarrow> pttrn \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process"
  ("(3_ \<triangleright> _./ _)" [101, 0, 100] 100)
translations
  "c \<triangleright> x. P" \<rightleftharpoons> "CONST UnicastInput c (\<lambda>x. P)"
syntax
  "_BroadcastInput" :: "pttrn \<Rightarrow> ('name, 'chan, 'val) process \<Rightarrow> ('name, 'chan, 'val) process"
  ("(3\<star> \<triangleright> _./ _)" [0, 100] 100)
translations
  "\<star> \<triangleright> x. P" \<rightleftharpoons> "CONST BroadcastInput (\<lambda>x. P)"

text \<open>
  This is all for processes.
\<close>

end
