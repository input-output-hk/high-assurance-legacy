theory Typed_Channels
  imports "HOL-Library.Countable" Channels
begin

typedecl 'a channel

axiomatization untyped_channel :: "'a channel \<Rightarrow> chan"
axiomatization typed_channel :: "chan \<Rightarrow> 'a channel"

text \<open>
  We require that \<^typ>\<open>'a channel\<close> is countable for any~\<open>'a\<close>, so that it is possible to send
  channels over channels.
\<close>

(* Countability of value types is talked about only later. *)

axiomatization channel_to_nat :: "'a channel \<Rightarrow> nat" where
  channel_to_nat_injectivity: "inj channel_to_nat"
instantiation channel :: (type) countable
begin
instance by (standard, intro exI) (fact channel_to_nat_injectivity)
end

(* The following says retroactively that \<open>val\<close> must be infinite. *)

axiomatization untyped_value :: "'a::countable \<Rightarrow> val" where
  untyped_value_injectivity: "inj untyped_value"
abbreviation typed_value :: "val \<Rightarrow> 'a::countable" where
  "typed_value \<equiv> inv untyped_value"

lemma typed_untyped_value [simp]: "typed_value (untyped_value V) = V"
  using untyped_value_injectivity by (fact inv_f_f)

end
