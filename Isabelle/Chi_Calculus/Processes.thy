section \<open>Processes\<close>

theory Processes
  imports Channels
begin

text \<open>
  The definition of the type of processes is fairly straightforward.
\<close>
(* FIXME: Discuss the differences to the Haskell version. *)

codatatype process =
  Stop ("\<zero>") |
  Send chan val (infix "\<triangleleft>" 100) |
  Receive chan "(val \<Rightarrow> process)" |
  Parallel process process (infixr "\<parallel>" 65) |
  NewChannel "(chan \<Rightarrow> process)" (binder "\<nu>" 100)

text \<open>
  The notation for \<^const>\<open>Receive\<close> cannot be declared with @{theory_text \<open>binder\<close>}, for the
  following reasons:

    \<^item> It does not allow binding multiple variables in one go (like in \<open>\<forall>x\<^sub>1 \<dots> x\<^sub>n. [\<dots>]\<close>).

    \<^item> It has an extra parameter (for the channel) before the binder.

  Therefore we introduce this notation using the low-level @{theory_text \<open>syntax\<close>} and
  @{theory_text \<open>translations\<close>} constructs.
\<close>

syntax
  "_Receive" :: "chan \<Rightarrow> pttrn \<Rightarrow> process \<Rightarrow> process"
  ("(3_ \<triangleright> _./ _)" [101, 0, 100] 100)
translations
  "a \<triangleright> x. p" \<rightleftharpoons> "CONST Receive a (\<lambda>x. p)"

text \<open>
  We define guarding of processes at the host-language level.
\<close>

abbreviation guard :: "[bool, process] \<Rightarrow> process" (infixr "?" 100) where
  "x ? p \<equiv> if x then p else \<zero>"

text \<open>
  This is all for processes.
\<close>

end
