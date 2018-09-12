theory Typed_Basic_Transition_System
  imports Basic_Transition_System Typed_Processes
begin

abbreviation
  typed_basic_out :: "['a channel, 'a::countable] \<Rightarrow> io_action"
where
  "typed_basic_out c V \<equiv> BasicOut (untyped_channel c) (untyped_value V)"
abbreviation
  typed_basic_in :: "['a channel, 'a::countable] \<Rightarrow> io_action"
where
  "typed_basic_in c V \<equiv> BasicIn (untyped_channel c) (untyped_value V)"
abbreviation
  typed_basic_out_action :: "['a channel, 'a::countable] \<Rightarrow> basic_action" (infix "\<triangleleft>\<degree>" 100)
where
  "c \<triangleleft>\<degree> V :: basic_action \<equiv> untyped_channel c \<triangleleft> untyped_value V"
abbreviation
  typed_basic_in_action :: "['a channel, 'a::countable] \<Rightarrow> basic_action" (infix "\<triangleright>\<degree>" 100)
where
  "c \<triangleright>\<degree> V \<equiv> untyped_channel c \<triangleright> untyped_value V"

abbreviation typed_opening :: "('a channel \<Rightarrow> process) \<Rightarrow> basic_residual" where
  "typed_opening \<P> \<equiv> \<lbrace>\<nu> a\<rbrace> \<P> (typed_channel a)"
syntax
  "_typed_opening" :: "pttrn \<Rightarrow> process \<Rightarrow> basic_residual"
  ("\<lbrace>\<nu>\<degree>_\<rbrace> _" [0, 51] 51)
translations
  "\<lbrace>\<nu>\<degree>a\<rbrace> P" \<rightleftharpoons> "CONST typed_opening (\<lambda>a. P)"

lemma typed_ltr: "typed_basic_out c V \<bowtie> typed_basic_in c V"
  by (fact ltr)
lemma typed_rtl: "typed_basic_in c V \<bowtie> typed_basic_out c V"
  by (fact rtl)

lemma typed_sending: "c \<triangleleft>\<degree> V \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft>\<degree> V\<rbrace> \<zero>"
  by (fact sending)
lemma typed_receiving: "c \<triangleright>\<degree> x. \<P> x \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleright>\<degree> V\<rbrace> \<P> V"
  using receiving and typed_untyped_value
  by metis
lemma typed_opening: "\<nu>\<degree>a. \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>a\<rbrace> \<P> a"
  by (fact opening)
lemma typed_opening_left: "P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>a\<rbrace> \<P> a \<Longrightarrow> P \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>a\<rbrace> \<P> a \<parallel> Q"
  by (fact opening_left)
lemma typed_opening_right: "Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>a\<rbrace> \<Q> a \<Longrightarrow> P \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>a\<rbrace> P \<parallel> \<Q> a"
  by (fact opening_right)
lemma typed_scoped_acting: "\<lbrakk>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>a\<rbrace> \<Q> a; \<And>a. \<Q> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<R> a\<rbrakk> \<Longrightarrow> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu>\<degree>a. \<R> a"
  by (simp add: scoped_acting)
lemma typed_scoped_opening: "\<lbrakk>P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>a\<rbrace> \<Q> a; \<And>a. \<Q> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>b\<rbrace> \<R> a b\<rbrakk> \<Longrightarrow> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>b\<rbrace> \<nu>\<degree>a. \<R> a b"
  by (simp add: scoped_opening)

lemma typed_opening_scope: "(\<And>a. \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>b\<rbrace> \<Q> a b) \<Longrightarrow> \<nu>\<degree>a. \<P> a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu>\<degree>b\<rbrace> \<nu>\<degree>a. \<Q> a b"
  by (simp add: opening_scope)

end
