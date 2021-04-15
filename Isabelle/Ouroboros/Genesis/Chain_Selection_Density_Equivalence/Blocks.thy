theory Blocks
imports Timing
begin

type_synonym block_body = string

type_synonym block = "slot \<times> block_body"

primrec bslot :: "block \<Rightarrow> slot" where
  "bslot (sl, _) = sl"

end
