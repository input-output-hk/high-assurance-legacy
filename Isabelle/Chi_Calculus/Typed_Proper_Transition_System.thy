theory Typed_Proper_Transition_System
  imports Proper_Transition_System Typed_Basic_Transition_System
begin

abbreviation
  typed_proper_in :: "['a channel, 'a::countable] \<Rightarrow> proper_action" (infix "\<triangleright>\<degree>" 100)
where
  "\<cc> \<triangleright>\<degree> \<vv> \<equiv> ProperIn (untyped_channel \<cc>) (untyped_value \<vv>)"

datatype 'a typed_output_rest =
  TypedWithoutOpening 'a process ("_\<rparr> _" [52, 51] 51) |
  TypedWithOpening "(chan \<Rightarrow> 'a typed_output_rest)"

(*
  We use the ordinary-font K to denote a function whose argument is untyped but whose resulting
  output rest is typed.
*)

primrec untyped_output_rest :: "'a::countable typed_output_rest \<Rightarrow> output_rest" where
  "untyped_output_rest (\<vv>\<rparr> p) = untyped_value \<vv>\<rparr> p" |
  "untyped_output_rest (TypedWithOpening K) = WithOpening (untyped_output_rest \<circ> K)"

abbreviation
  typed_with_opening :: "('a channel \<Rightarrow> 'b typed_output_rest) \<Rightarrow> 'b typed_output_rest"
  (binder "\<nu>\<degree>" 51)
where
  "\<nu>\<degree>\<aa>. \<KK> \<aa> \<equiv> TypedWithOpening (\<KK> \<circ> typed_channel)"

abbreviation
  typed_output :: "['a channel, 'a::countable typed_output_rest] \<Rightarrow> proper_residual"
  ("\<lparr>_ \<triangleleft>\<degree> _" [0, 51] 51)
where
  "\<lparr>\<cc> \<triangleleft>\<degree> \<kk> \<equiv> \<lparr>untyped_channel \<cc> \<triangleleft> untyped_output_rest \<kk>"

lemma typed_output_without_opening: "p \<longmapsto>\<^sub>\<flat>\<lbrace>\<cc> \<triangleleft>\<degree> \<vv>\<rbrace> q \<Longrightarrow> p \<longmapsto>\<^sub>\<sharp>\<lparr>\<cc> \<triangleleft>\<degree> \<vv>\<rparr> q"
  by (simp add: output_without_opening)
lemma typed_output_with_opening:
  "\<lbrakk>p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<QQ> \<aa>; \<And>\<aa>. \<QQ> \<aa> \<longmapsto>\<^sub>\<sharp>\<lparr>\<cc> \<triangleleft>\<degree> \<KK> \<aa>\<rbrakk> \<Longrightarrow> p \<longmapsto>\<^sub>\<sharp>\<lparr>\<cc> \<triangleleft>\<degree> \<nu>\<degree>\<aa>. \<KK> \<aa>"
  by (simp add: output_with_opening)

end
