section \<open>Processes\<close>

theory Processes
  imports Main
begin

text \<open>
  We introduce types for channels and values.
\<close>

typedecl chan
typedecl val

text \<open>
  The definition of the type of processes is fairly straightforward.
\<close>

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
  "c \<triangleright> x. P" \<rightleftharpoons> "CONST Receive c (\<lambda>x. P)"

text \<open>
  This is all for processes.
\<close>

end
