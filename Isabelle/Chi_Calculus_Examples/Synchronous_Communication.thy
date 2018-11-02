section \<open>Synchronous Communication Layer\<close>

theory Synchronous_Communication
  imports
    "HOL-Library.BNF_Corec"
    Chi_Calculus.Typed_Processes
    Chi_Calculus.Typed_Basic_Transition_System
    Chi_Calculus.Basic_Weak_Bisimulation
begin

subsection \<open>Synchronous channels\<close>

type_synonym 'a sync_channel = "'a channel channel channel"

subsection \<open>Communication primitives\<close>

abbreviation
  sync_send :: "['a::countable sync_channel, 'a, process] \<Rightarrow> process" ("(3_ \<triangleleft>\<^sup>\<leftrightarrow> _./ _)" [101, 0, 100] 100)
where
  "sync_send c v P \<equiv> \<nu>\<degree> sreply. (c \<triangleleft>\<degree> sreply \<parallel> sreply \<triangleright>\<degree> rreply. (rreply \<triangleleft>\<degree> v \<parallel> P))"

abbreviation
  sync_recv :: "['a::countable sync_channel, 'a \<Rightarrow> process] \<Rightarrow> process"
where
  "sync_recv c \<P> \<equiv> c \<triangleright>\<degree> sreply. \<nu>\<degree> rreply. (sreply \<triangleleft>\<degree> rreply \<parallel> rreply \<triangleright>\<degree> x. \<P> x)"

syntax
  "_sync_recv" :: "['a sync_channel, pttrn, process]\<Rightarrow> process"
  ("(3_ \<triangleright>\<^sup>\<leftrightarrow> _./ _)" [101, 0, 100] 100)
translations
  "c \<triangleright>\<^sup>\<leftrightarrow> x. P" \<rightleftharpoons> "CONST sync_recv c (\<lambda>x. P)"

subsection \<open>Properties\<close>

(* TODO: Prove it. *)
lemma sync_communication: "\<nu>\<degree> c. (c \<triangleleft>\<^sup>\<leftrightarrow> v. P \<parallel> c \<triangleright>\<^sup>\<leftrightarrow> x. \<Q> x) \<approx>\<^sub>\<flat> \<nu>\<degree> c. (P \<parallel> \<Q> v)" sorry

subsection \<open>Examples\<close>

text \<open>
  The Computer Scientist (from "An Introduction to Milner's CCS" (Aceto-Larsen, 2005)).
\<close>

datatype coffee = Coffee

instantiation coffee :: countable
begin
instance by countable_datatype
end

datatype coin = Coin

instantiation coin :: countable
begin
instance by countable_datatype
end

datatype publication = Publication

instantiation publication :: countable
begin
instance by countable_datatype
end

corec
  coffee_machine :: "coin sync_channel \<Rightarrow> coffee sync_channel \<Rightarrow> process"
where
  "coffee_machine coin coffee = coin \<triangleright>\<^sup>\<leftrightarrow> _.coffee \<triangleleft>\<^sup>\<leftrightarrow> Coffee. coffee_machine coin coffee"

corec
  computer_scientist :: "publication sync_channel \<Rightarrow> coin sync_channel \<Rightarrow> coffee sync_channel \<Rightarrow> process"
where
  "computer_scientist pub coin coffee = pub \<triangleleft>\<^sup>\<leftrightarrow> Publication. coin \<triangleleft>\<^sup>\<leftrightarrow> Coin. coffee \<triangleright>\<^sup>\<leftrightarrow> _. computer_scientist pub coin coffee"

abbreviation
  impl :: "publication sync_channel \<Rightarrow> process"
where
  "impl pub \<equiv> \<nu>\<degree> coin coffee. (computer_scientist pub coin coffee \<parallel> coffee_machine coin coffee)"

corec
  spec :: "publication sync_channel \<Rightarrow> process"
where
  "spec pub = pub \<triangleleft>\<^sup>\<leftrightarrow> Publication. spec pub"

(* TODO: Prove it. *)
lemma correctness_proof: "spec pub \<approx>\<^sub>\<flat> impl pub" sorry

end
