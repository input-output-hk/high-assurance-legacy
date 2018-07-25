section \<open>Processes\<close>

theory Processes
  imports Main
begin

text \<open>
  The definition of the type of processes is fairly straightforward.
\<close>

codatatype ('chan, 'val) process =
  Stop ("\<zero>") |
  Send 'chan 'val (infix "\<triangleleft>" 100) |
  Receive 'chan "('val \<Rightarrow> ('chan, 'val) process)" |
  Parallel "(('chan, 'val) process)" "(('chan, 'val) process)" (infixr "\<parallel>" 65) |
  NewChannel "('chan \<Rightarrow> ('chan, 'val) process)" (binder "\<nu>" 100)

(*
  It might be good to never use a concrete channel type and introduce global channels by passing
  them as function arguments.
*)

text \<open>
  The notation for \<^const>\<open>Receive\<close> cannot be declared with @{theory_text \<open>binder\<close>}, for the
  following reasons:

    \<^item> It does not allow binding multiple variables in one go (like in \<open>\<forall>x\<^sub>1 \<dots> x\<^sub>n. [\<dots>]\<close>).

    \<^item> It has an extra parameter (for the channel) before the binder.

  Therefore we introduce this notation using the low-level @{theory_text \<open>syntax\<close>} and
  @{theory_text \<open>translations\<close>} constructs.
\<close>

syntax
  "_Receive" :: "'chan \<Rightarrow> pttrn \<Rightarrow> ('chan, 'val) process \<Rightarrow> ('chan, 'val) process"
  ("(3_ \<triangleright> _./ _)" [101, 0, 100] 100)
translations
  "c \<triangleright> x. P" \<rightleftharpoons> "CONST Receive c (\<lambda>x. P)"

text \<open>
  This is all for processes.
\<close>

end
