section \<open> Timing \<close>

theory Timing
imports Main
begin

text \<open>
  As defined in Section 3 of @{cite "genesis-paper"}, we model the concept of @{emph \<open>slot\<close>} as a
  natural number:
\<close>

type_synonym slot = nat

text \<open>
  and assume that the slot associated to the genesis block is \<open>0\<close> (since it is assumed that the
  protocol starts when the global time is \<open>\<tau> = 0\<close>):
\<close>

abbreviation (input) genesis_slot :: slot where
  "genesis_slot \<equiv> 0" (* NOTE: In the real implementation the first block starts at 0 *)

end
