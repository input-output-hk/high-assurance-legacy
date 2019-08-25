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
  Send \<open>chan\<close> \<open>val\<close> (infix "\<triangleleft>" 100) |
  Receive \<open>chan\<close> \<open>val \<Rightarrow> process\<close> |
  Parallel \<open>process\<close> \<open>process\<close> (infixr "\<parallel>" 65) |
  NewChannel \<open>chan \<Rightarrow> process\<close> (binder "\<nu> " 100)

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
  We define parallel composition over a list of processes.
\<close>

primrec general_parallel :: "['a \<Rightarrow> process, 'a list] \<Rightarrow> process" where
  "general_parallel _ [] = \<zero>" |
  "general_parallel f (x # xs) = f x \<parallel> general_parallel f xs"

text \<open>
  We define a notation for repeated parallel composition combined with mapping. Since this notation
  clashes with \<open>HOL.Groups_List._prod_list\<close>, we have to remove the latter.
\<close>

no_syntax
  "_prod_list" :: "pttrn => 'a list => 'b => 'b" ("(3\<Prod>_\<leftarrow>_. _)" [0, 51, 10] 10)
syntax
  "_general_parallel" :: "pttrn => 'a list => process => process" ("(3\<Prod>_\<leftarrow>_. _)" [0, 0, 100] 100)
translations
  "\<Prod>x\<leftarrow>xs. p" \<rightleftharpoons> "CONST general_parallel (\<lambda>x. p) xs"

lemma general_parallel_conversion_deferral:
  shows "\<Prod>y\<leftarrow>map f xs. P y = \<Prod>x\<leftarrow>xs. P (f x)"
  by (induction xs) simp_all

text \<open>
  This is all for processes.
\<close>

end
