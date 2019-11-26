theory Typed_Proper_Transition_System
  imports Proper_Transition_System Typed_Basic_Transition_System
begin

abbreviation
  typed_proper_in :: "['a channel, 'a::countable] \<Rightarrow> proper_action" (infix \<open>\<triangleright>\<degree>\<close> 100)
where
  "\<aa> \<triangleright>\<degree> \<xx> \<equiv> ProperIn (untyped_channel \<aa>) (untyped_value \<xx>)"

datatype ('a, 'p) typed_output_rest =
  TypedWithoutOpening \<open>'a\<close> \<open>'p\<close> (\<open>_\<rparr> _\<close> [52, 51] 51) |
  TypedWithOpening \<open>chan \<Rightarrow> ('a, 'p) typed_output_rest\<close>

(*
  We use the ordinary-font K to denote a function whose argument is untyped but whose resulting
  output rest is typed.
*)

primrec untyped_output_rest :: "('a::countable, 'p) typed_output_rest \<Rightarrow> 'p output_rest" where
  "untyped_output_rest (\<xx>\<rparr> p) = untyped_value \<xx>\<rparr> p" |
  "untyped_output_rest (TypedWithOpening K) = WithOpening (untyped_output_rest \<circ> K)"

abbreviation
  typed_with_opening :: "('a channel \<Rightarrow> ('b, 'p) typed_output_rest) \<Rightarrow> ('b, 'p) typed_output_rest"
  (binder "\<nu>\<degree>" 51)
where
  "\<nu>\<degree>\<aa>. \<KK> \<aa> \<equiv> TypedWithOpening (\<KK> \<circ> typed_channel)"

abbreviation
  typed_output :: "['a channel, ('a::countable, 'p) typed_output_rest] \<Rightarrow> 'p proper_residual"
  (\<open>\<lparr>_ \<triangleleft>\<degree> _\<close> [0, 51] 51)
where
  "\<lparr>\<aa> \<triangleleft>\<degree> \<kk> \<equiv> \<lparr>untyped_channel \<aa> \<triangleleft> untyped_output_rest \<kk>"

lemma typed_output_without_opening: "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<aa> \<triangleleft>\<degree> \<xx>\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<aa> \<triangleleft>\<degree> \<xx>\<rparr> q"
  by (simp add: output_without_opening)
lemma typed_output_with_opening:
  "\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<QQ> \<bb>; \<And>\<bb>. \<QQ> \<bb> \<rightarrow>\<^sub>\<sharp>\<lparr>\<aa> \<triangleleft>\<degree> \<KK> \<bb>\<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<aa> \<triangleleft>\<degree> \<nu>\<degree>\<bb>. \<KK> \<bb>"
  by (simp add: output_with_opening)

end
