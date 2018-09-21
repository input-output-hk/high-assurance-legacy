theory Typed_Basic_Transition_System
  imports Basic_Transition_System Typed_Processes
begin

abbreviation
  typed_basic_out :: "['a channel, 'a::countable] \<Rightarrow> io_action"
where
  "typed_basic_out \<cc> \<vv> \<equiv> BasicOut (untyped_channel \<cc>) (untyped_value \<vv>)"
abbreviation
  typed_basic_in :: "['a channel, 'a::countable] \<Rightarrow> io_action"
where
  "typed_basic_in \<cc> \<vv> \<equiv> BasicIn (untyped_channel \<cc>) (untyped_value \<vv>)"
abbreviation
  typed_basic_out_action :: "['a channel, 'a::countable] \<Rightarrow> basic_action" (infix "\<triangleleft>\<degree>" 100)
where
  "\<cc> \<triangleleft>\<degree> \<vv> :: basic_action \<equiv> untyped_channel \<cc> \<triangleleft> untyped_value \<vv>"
abbreviation
  typed_basic_in_action :: "['a channel, 'a::countable] \<Rightarrow> basic_action" (infix "\<triangleright>\<degree>" 100)
where
  "\<cc> \<triangleright>\<degree> \<vv> \<equiv> untyped_channel \<cc> \<triangleright> untyped_value \<vv>"

abbreviation typed_opening :: "('a channel \<Rightarrow> process) \<Rightarrow> basic_residual" where
  "typed_opening \<PP> \<equiv> \<lbrace>\<nu> a\<rbrace> \<PP> (typed_channel a)"
syntax
  "_typed_opening" :: "pttrn \<Rightarrow> process \<Rightarrow> basic_residual"
  ("\<lbrace>\<nu>\<degree>_\<rbrace> _" [0, 51] 51)
translations
  "\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<pp>" \<rightleftharpoons> "CONST typed_opening (\<lambda>\<aa>. \<pp>)"

lemma typed_ltr: "typed_basic_out \<cc> \<vv> \<bowtie> typed_basic_in \<cc> \<vv>"
  by (fact ltr)
lemma typed_rtl: "typed_basic_in \<cc> \<vv> \<bowtie> typed_basic_out \<cc> \<vv>"
  by (fact rtl)

lemma typed_sending: "\<cc> \<triangleleft>\<degree> \<vv> \<longmapsto>\<^sub>\<flat>\<lbrace>\<cc> \<triangleleft>\<degree> \<vv>\<rbrace> \<zero>"
  by (fact sending)
lemma typed_receiving: "\<cc> \<triangleright>\<degree> \<xx>. \<PP> \<xx> \<longmapsto>\<^sub>\<flat>\<lbrace>\<cc> \<triangleright>\<degree> \<vv>\<rbrace> \<PP> \<vv>"
  using receiving and typed_untyped_value
  by metis
lemma typed_opening: "\<nu>\<degree>\<aa>. \<PP> \<aa> \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<PP> \<aa>"
  by (fact opening)
lemma typed_opening_left: "p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<PP> \<aa> \<Longrightarrow> p \<parallel> q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<PP> \<aa> \<parallel> q"
  by (fact opening_left)
lemma typed_opening_right: "q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<QQ> \<aa> \<Longrightarrow> p \<parallel> q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> p \<parallel> \<QQ> \<aa>"
  by (fact opening_right)
lemma typed_scoped_acting: "\<lbrakk>p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<QQ> \<aa>; \<And>\<aa>. \<QQ> \<aa> \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<RR> \<aa>\<rbrakk> \<Longrightarrow> p \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu>\<degree>\<aa>. \<RR> \<aa>"
  by (simp add: scoped_acting)
lemma typed_scoped_opening: "\<lbrakk>p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<QQ> \<aa>; \<And>\<aa>. \<QQ> \<aa> \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<RR> \<aa> \<bb>\<rbrakk> \<Longrightarrow> p \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<nu>\<degree>\<aa>. \<RR> \<aa> \<bb>"
  by (simp add: scoped_opening)

lemma typed_opening_scope: "(\<And>\<aa>. \<PP> \<aa> \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<QQ> \<aa> \<bb>) \<Longrightarrow> \<nu>\<degree>\<aa>. \<PP> \<aa> \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<nu>\<degree>\<aa>. \<QQ> \<aa> \<bb>"
  by (simp add: opening_scope)

end
