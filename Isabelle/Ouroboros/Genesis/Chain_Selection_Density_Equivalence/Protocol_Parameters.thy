section \<open> Protocol parameters \<close>

theory Protocol_Parameters
imports Complex_Main
begin

text \<open>
  The protocol depends on a number of parameters, among others are the following:

  \<^item> \<open>k\<close>: Establishes how deep in the chain (in terms of number of blocks) a transaction needs to be
    in order to be declared as stable.
  \<^item> \<open>f\<close>: The `active slot coefficient'. Establishes the probability that at least one stakeholder
    is elected as a slot leader in each slot, that is, the probability that a slot is not empty.
    Must be a strictly positive probability.
\<close>

locale protocol_parameters =
  fixes k :: nat
    and f :: real
  assumes f_non_zero_probability: "f \<in> {0<..1}"
begin

text \<open>
  According to Definition 21.3 in @{cite "cardano-consensus-tr"} (which is based on the analysis in
  Section 4 of @{cite "genesis-praos-parametrization"}), the default value for the Genesis window
  size is set to \<open>3k/f\<close>:
\<close>

abbreviation default_window_size :: nat where
  "default_window_size \<equiv> nat \<lceil>3 * k / f\<rceil>"

text \<open>
  We can show that the default value is at least \<open>k\<close>:
\<close>

lemma default_window_greater_or_equal_than_k:
  shows "default_window_size \<ge> k"
proof -
  have "default_window_size \<ge> 3 * k"
    using f_non_zero_probability
    by (smt divide_numeral_1 frac_le greaterThanAtMost_iff nat_le_0 of_nat_ceiling of_nat_le_iff
        zero_less_ceiling)
  then show ?thesis
    by linarith
qed

end

end

