theory Typed_Basic_Transition_System
  imports Basic_Transition_System Typed_Processes
begin

abbreviation
  typed_basic_out :: "['a channel, 'a::countable] \<Rightarrow> io_action"
where
  "typed_basic_out \<aa> \<xx> \<equiv> BasicOut (untyped_channel \<aa>) (untyped_value \<xx>)"
abbreviation
  typed_basic_in :: "['a channel, 'a::countable] \<Rightarrow> io_action"
where
  "typed_basic_in \<aa> \<xx> \<equiv> BasicIn (untyped_channel \<aa>) (untyped_value \<xx>)"
abbreviation
  typed_basic_out_action :: "['a channel, 'a::countable] \<Rightarrow> basic_action" (infix \<open>\<triangleleft>\<degree>\<close> 100)
where
  "\<aa> \<triangleleft>\<degree> \<xx> :: basic_action \<equiv> untyped_channel \<aa> \<triangleleft> untyped_value \<xx>"
abbreviation
  typed_basic_in_action :: "['a channel, 'a::countable] \<Rightarrow> basic_action" (infix \<open>\<triangleright>\<degree>\<close> 100)
where
  "\<aa> \<triangleright>\<degree> \<xx> \<equiv> untyped_channel \<aa> \<triangleright> untyped_value \<xx>"

abbreviation typed_opening :: "('a channel \<Rightarrow> 'p) \<Rightarrow> 'p basic_residual" where
  "typed_opening \<PP> \<equiv> \<lbrace>\<nu> a\<rbrace> \<PP> (typed_channel a)"
syntax
  "_typed_opening" :: "pttrn \<Rightarrow> process \<Rightarrow> 'p basic_residual"
  (\<open>\<lbrace>\<nu>\<degree>_\<rbrace> _\<close> [0, 51] 51)
translations
  "\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<pp>" \<rightleftharpoons> "CONST typed_opening (\<lambda>\<aa>. \<pp>)"
print_translation \<open>
  [
    Syntax_Trans.preserve_binder_abs_tr'
      @{const_syntax typed_opening}
      @{syntax_const "_typed_opening"}
  ]
\<close>
(* FIXME:
  The @{command print_translation} part will only work once we have changed @{command abbreviation}
  to @{command definition}.
*)

lemma typed_ltr: "typed_basic_out \<aa> \<xx> \<bowtie> typed_basic_in \<aa> \<xx>"
  by (fact ltr)
lemma typed_rtl: "typed_basic_in \<aa> \<xx> \<bowtie> typed_basic_out \<aa> \<xx>"
  by (fact rtl)

lemma typed_sending: "\<aa> \<triangleleft>\<degree> \<xx> \<rightarrow>\<^sub>\<flat>\<lbrace>\<aa> \<triangleleft>\<degree> \<xx>\<rbrace> \<zero>"
  by (fact sending)
lemma typed_receiving: "\<aa> \<triangleright>\<degree> \<xx>. \<PP> \<xx> \<rightarrow>\<^sub>\<flat>\<lbrace>\<aa> \<triangleright>\<degree> \<xx>\<rbrace> \<PP> \<xx>"
  using receiving and typed_untyped_value
  by metis
lemma typed_opening: "\<nu>\<degree>\<aa>. \<PP> \<aa> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<PP> \<aa>"
  by (fact scope_opening)
lemma typed_opening_left: "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<PP> \<aa> \<Longrightarrow> p \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<PP> \<aa> \<parallel> q"
  by (fact opening_left)
lemma typed_opening_right: "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<QQ> \<aa> \<Longrightarrow> p \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> p \<parallel> \<QQ> \<aa>"
  by (fact opening_right)
lemma typed_scoped_acting: "\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<QQ> \<aa>; \<And>\<aa>. \<QQ> \<aa> \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<RR> \<aa>\<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu>\<degree>\<aa>. \<RR> \<aa>"
  by (simp add: scoped_acting)
lemma typed_scoped_opening: "\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<aa>\<rbrace> \<QQ> \<aa>; \<And>\<aa>. \<QQ> \<aa> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<RR> \<aa> \<bb>\<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<nu>\<degree>\<aa>. \<RR> \<aa> \<bb>"
  by (simp add: scoped_opening)

lemma typed_opening_scope: "(\<And>\<aa>. \<PP> \<aa> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<QQ> \<aa> \<bb>) \<Longrightarrow> \<nu>\<degree>\<aa>. \<PP> \<aa> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu>\<degree>\<bb>\<rbrace> \<nu>\<degree>\<aa>. \<QQ> \<aa> \<bb>"
  by (simp add: opening_scope)

end
