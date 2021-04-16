theory Blocks
imports Timing
begin

typedecl block_body

type_synonym block = "slot \<times> block_body"

primrec bslot :: "block \<Rightarrow> slot" where
  "bslot (sl, _) = sl"

end
