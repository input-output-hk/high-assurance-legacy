section \<open>Processes\<close>

theory Processes
  imports Main
begin

text \<open>
  A communication medium is either a channel, providing unicast communication, or the ether,
  providing broadcast communication.
\<close>

datatype 'chan medium =
  Unicast 'chan ("\<cdot>_" [1000] 1000) |
  Broadcast ("\<star>")

text \<open>
  The definition of the type of processes is fairly straightforward.
\<close>

datatype ('name, 'chan, 'val) process =
  Stop ("\<zero>") |
  Send "('chan medium)" 'val (infix "\<triangleleft>" 100) |
  Receive "('chan medium)" "('val \<Rightarrow> ('name, 'chan, 'val) process)" |
  Parallel "(('name, 'chan, 'val) process)" "(('name, 'chan, 'val) process)" (infixr "\<parallel>" 65) |
  NewChannel "('chan \<Rightarrow> ('name, 'chan, 'val) process)" (binder "\<nu>" 100) |
  Invoke 'name 'val ("\<langle>_\<rangle> _" [0, 100] 100)

(*
  It might be good to never use a concrete channel type and introduce global channels by passing
  them as function arguments.
*)

text \<open>
  The notation for \<^const>\<open>Receive\<close> cannot be declared with @{theory_text \<open>binder\<close>}, for the
  following reasons:

    \<^item> It does not allow binding multiple variables in one go (like in \<open>\<forall>x\<^sub>1 \<dots> x\<^sub>n. [\<dots>]\<close>).

    \<^item> It has an extra parameter (for the medium) before the binder.

  Therefore we introduce this notation using the low-level @{theory_text \<open>syntax\<close>} and
  @{theory_text \<open>translations\<close>} constructs.
\<close>

syntax
  "_Receive" :: "
    'chan medium \<Rightarrow>
    pttrn \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process"
  ("(3_ \<triangleright> _./ _)" [101, 0, 100] 100)
translations
  "m \<triangleright> x. P" \<rightleftharpoons> "CONST Receive m (\<lambda>x. P)"

text \<open>
  This is all for processes.
\<close>

end
