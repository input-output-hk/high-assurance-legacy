section \<open>Actions\<close>

theory "Thorn_Calculus-Actions"
imports
  "Thorn_Calculus-Foundations"
begin

datatype io_kind =
  Sending |
  Receiving

datatype action =
  IO \<open>io_kind\<close> \<open>chan family\<close> \<open>nat\<close> \<open>val family\<close> |
  Communication (\<open>\<tau>\<close>)

abbreviation
  sending :: "chan family \<Rightarrow> nat \<Rightarrow> val family \<Rightarrow> action"
  (\<open>(_ \<triangleleft>/ \<star>()\<^bsup>_\<^esup> _)\<close> [53, 0, 53] 52)
where
  "A \<triangleleft> \<star>\<^bsup>n\<^esup> X \<equiv> IO Sending A n X"

abbreviation
  receiving :: "chan family \<Rightarrow> nat \<Rightarrow> val family \<Rightarrow> action"
  (\<open>(_ \<triangleright>/ \<star>()\<^bsup>_\<^esup> _)\<close> [53, 0, 53] 52)
where
  "A \<triangleright> \<star>\<^bsup>n\<^esup> X \<equiv> IO Receiving A n X"

end
