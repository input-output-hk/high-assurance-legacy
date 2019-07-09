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
  NewChannel \<open>chan \<Rightarrow> process\<close> (binder "\<nu>" 100)

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

abbreviation parallel_list :: "process list \<Rightarrow> process" where
  "parallel_list ps \<equiv> foldr (\<parallel>) ps \<zero>"

text \<open>
  We define a notation for repeated parallel composition combined with mapping. This notation is
  analogous to \<open>HOL.Groups_List._prod_list\<close>, which we have to remove in order to avoid a clash.
\<close>

no_syntax
  "_prod_list" :: "pttrn => 'a list => 'b => 'b" ("(3\<Prod>_\<leftarrow>_. _)" [0, 51, 10] 10)
syntax
  "_parallel_list" :: "pttrn => 'a list => process => process" ("(3\<Prod>_\<leftarrow>_. _)" [0, 0, 100] 100)
translations
  "\<Prod>x\<leftarrow>xs. p" \<rightleftharpoons> "CONST parallel_list (CONST map (\<lambda>x. p) xs)"

(* FIXME:
  Every occurrence of “preservation” in the following part (including in comments) should be
  replaced by “compatibility” later.
*)

text \<open>
  We prove some lemmas from which we can construct \<open>\<Prod>\<close>-preservation laws for different bisimilarity
  relations.
\<close>

lemma map_preservation:
  fixes R (infix "\<sim>" 50)
  assumes "\<And>x. f x \<sim> g x"
  shows "list_all2 (\<sim>) (map f xs) (map g xs)"
  using assms by (induction xs) simp_all

lemma parallel_list_preservation:
  fixes R (infix "\<sim>" 50)
  assumes bisimilarity_reflexivity_rule:
    "\<And>p. p \<sim> p"
  assumes parallel_preservation:
    "\<And>p\<^sub>1 p\<^sub>2 q\<^sub>1 q\<^sub>2. \<lbrakk>p\<^sub>1 \<sim> p\<^sub>2; q\<^sub>1 \<sim> q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<sim> p\<^sub>2 \<parallel> q\<^sub>2"
  assumes are_bisimilar:
    "list_all2 (\<sim>) xs ys"
  shows
    "parallel_list xs \<sim> parallel_list ys"
  using are_bisimilar and bisimilarity_reflexivity_rule and parallel_preservation
  by induction simp_all
  
text \<open>
  This is all for processes.
\<close>

end
