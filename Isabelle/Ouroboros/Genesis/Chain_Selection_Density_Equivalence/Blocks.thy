section \<open> Blocks \<close>

theory Blocks
imports Timing
begin

text \<open>
  For the purposes of this work, we regard a @{emph \<open>block\<close>} as simply a pair comprised by the
  slot in which the block was created and a block body (which is left undefined):
\<close>

(* typedecl block_body *)
type_synonym block_body = unit \<comment> \<open>TODO: Only for testing, change to \<open>typedecl block_body\<close>\<close>

type_synonym block = "slot \<times> block_body"

text \<open>
  We also define an accessor function for obtaining the slot associated to a block:
\<close>

primrec bslot :: "block \<Rightarrow> slot" where
  "bslot (sl, _) = sl"

end
