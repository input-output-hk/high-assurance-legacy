theory Typed_Processes
  imports Processes Typed_Channels
begin

abbreviation typed_send :: "['a channel, 'a::countable] \<Rightarrow> process" (infix "\<triangleleft>\<degree>" 100) where
  "c \<triangleleft>\<degree> V \<equiv> untyped_channel c \<triangleleft> untyped_value V"
abbreviation typed_receive :: "['a channel, 'a::countable \<Rightarrow> process] \<Rightarrow> process" where
  "typed_receive c \<P> \<equiv> untyped_channel c \<triangleright> x. \<P> (typed_value x)"
syntax
  "_typed_receive" :: "'a::countable channel \<Rightarrow> pttrn \<Rightarrow> process \<Rightarrow> process"
  ("(3_ \<triangleright>\<degree> _./ _)" [101, 0, 100] 100)
translations
  "c \<triangleright>\<degree> x. P" \<rightleftharpoons> "CONST typed_receive c (\<lambda>x. P)"
abbreviation typed_new_channel :: "('a channel \<Rightarrow> process) \<Rightarrow> process" (binder "\<nu>\<degree>" 100) where
  "\<nu>\<degree>a. \<P> a \<equiv> \<nu> a. \<P> (typed_channel a)"

end
