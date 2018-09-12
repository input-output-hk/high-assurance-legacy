theory Typed_Proper_Transition_System
  imports Proper_Transition_System Typed_Basic_Transition_System
begin

abbreviation
  typed_proper_in :: "['a channel, 'a::countable] \<Rightarrow> proper_action" (infix "\<triangleright>\<degree>" 100)
where
  "c \<triangleright>\<degree> V \<equiv> ProperIn (untyped_channel c) (untyped_value V)"

datatype 'a typed_output_rest =
  TypedWithoutOpening 'a process ("_\<rparr> _" [52, 51] 51) |
  TypedWithOpening "(chan \<Rightarrow> 'a typed_output_rest)"

primrec untyped_output_rest :: "'a::countable typed_output_rest \<Rightarrow> output_rest" where
  "untyped_output_rest (V\<rparr> P) = untyped_value V\<rparr> P" |
  "untyped_output_rest (TypedWithOpening \<K>) = WithOpening (untyped_output_rest \<circ> \<K>)"

abbreviation
  typed_with_opening :: "('a channel \<Rightarrow> 'b typed_output_rest) \<Rightarrow> 'b typed_output_rest"
  (binder "\<nu>\<degree>" 51)
where
  "\<nu>\<degree>a. \<K> a \<equiv> TypedWithOpening (\<K> \<circ> typed_channel)"

abbreviation
  typed_output :: "['a channel, 'a::countable typed_output_rest] \<Rightarrow> proper_residual"
  ("\<lparr>_ \<triangleleft>\<degree> _" [0, 51] 51)
where
  "\<lparr>c \<triangleleft>\<degree> K \<equiv> \<lparr>untyped_channel c \<triangleleft> untyped_output_rest K"

lemma typed_output_without_opening: "P \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft>\<degree> V\<rbrace> Q \<Longrightarrow> P \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft>\<degree> V\<rparr> Q"
  by (simp add: output_without_opening)
lemma typed_output_with_opening:
  "\<lbrakk>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>a\<rbrace> \<Q> a; \<And>a. \<Q> a \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft>\<degree> \<K> a\<rbrakk> \<Longrightarrow> P \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft>\<degree> \<nu>\<degree>a. \<K> a"
  by (simp add: output_with_opening)

end
