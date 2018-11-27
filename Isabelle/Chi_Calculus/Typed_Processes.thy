theory Typed_Processes
  imports Processes Typed_Channels
begin

abbreviation typed_send :: "['a channel, 'a::countable] \<Rightarrow> process" (infix "\<triangleleft>\<degree>" 100) where
  "\<aa> \<triangleleft>\<degree> \<xx> \<equiv> untyped_channel \<aa> \<triangleleft> untyped_value \<xx>"
abbreviation typed_receive :: "['a channel, 'a::countable \<Rightarrow> process] \<Rightarrow> process" where
  "typed_receive \<aa> \<PP> \<equiv> untyped_channel \<aa> \<triangleright> x. \<PP> (typed_value x)"
syntax
  "_typed_receive" :: "'a::countable channel \<Rightarrow> pttrn \<Rightarrow> process \<Rightarrow> process"
  ("(3_ \<triangleright>\<degree> _./ _)" [101, 0, 100] 100)
translations
  "\<aa> \<triangleright>\<degree> \<xx>. \<pp>" \<rightleftharpoons> "CONST typed_receive \<aa> (\<lambda>\<xx>. \<pp>)"
abbreviation typed_new_channel :: "('a channel \<Rightarrow> process) \<Rightarrow> process" (binder "\<nu>\<degree>" 100) where
  "\<nu>\<degree>\<aa>. \<PP> \<aa> \<equiv> \<nu> a. \<PP> (typed_channel a)"

end
