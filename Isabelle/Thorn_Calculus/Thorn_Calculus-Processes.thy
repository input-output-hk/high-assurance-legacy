section \<open>Processes\<close>

theory "Thorn_Calculus-Processes"
imports
  "Transition_Systems-New.Transition_Systems-Foundations" \<comment> \<open>for the \<^const>\<open>compower\<close> notation\<close>
  "Thorn_Calculus-Foundations"
begin

ML_file \<open>binder_preservation.ML\<close>

codatatype process =
  Stop |
  Send \<open>chan\<close> \<open>val\<close> |
  Receive \<open>chan\<close> \<open>val \<Rightarrow> process\<close> |
  Parallel \<open>process\<close> \<open>process\<close> |
  NewChannel \<open>chan \<Rightarrow> process\<close>

text \<open>
  We use \<^theory_text>\<open>abbreviation\<close> in the following, because with \<^theory_text>\<open>definition\<close> unfolding a
  \<^term>\<open>\<Delta>\<close>-application would not give us an application of one of the entities below but its
  unfolding.

  A probably even better explanation is that the following declarations are just for introducing
  syntactic sugar.
\<close>

abbreviation
  stop :: "process family" (\<open>\<zero>\<close>)
where
  "stop \<equiv> (\<lambda>_. Stop)"
abbreviation
  send :: "chan family \<Rightarrow> val family \<Rightarrow> process family" (infix \<open>\<triangleleft>\<close> 52)
where
  "send A X \<equiv> (\<lambda>e. Send (A e) (X e))"
abbreviation
  receive :: "chan family \<Rightarrow> (val \<Rightarrow> process family) \<Rightarrow> process family"
where
  "receive A \<P> \<equiv> (\<lambda>e. Receive (A e) (\<lambda>x. \<P> x e))"
abbreviation
  parallel :: "process family \<Rightarrow> process family \<Rightarrow> process family" (infixr \<open>\<parallel>\<close> 51)
where
  "parallel P Q \<equiv> (\<lambda>e. Parallel (P e) (Q e))"
abbreviation
  new_channel :: "(chan \<Rightarrow> process family) \<Rightarrow> process family" (binder \<open>\<nu> \<close> 52)
where
  "new_channel \<P> \<equiv> (\<lambda>e. NewChannel (\<lambda>a. \<P> a e))"

text \<open>
  The notation for \<^const>\<open>receive\<close> cannot be declared with @{theory_text \<open>binder\<close>}, for the
  following reasons:

    \<^item> It does not allow binding multiple variables in one go (like in \<open>\<forall>x\<^sub>1 \<dots> x\<^sub>n. _\<close>).

    \<^item> It has an extra parameter (for the channel family) before the binder.

  Therefore we introduce this notation using the low-level @{theory_text \<open>syntax\<close>},
  @{theory_text \<open>translations\<close>}, and @{theory_text \<open>print_translation\<close>} constructs.
\<close>

syntax
  "_receive" :: "chan family \<Rightarrow> pttrn \<Rightarrow> process family \<Rightarrow> process family"
  (\<open>(3_ \<triangleright> _./ _)\<close> [53, 0, 52] 52)
translations
  "A \<triangleright> x. P" \<rightleftharpoons> "CONST receive A (\<lambda>x. P)"
print_translation \<open>
  [preserve_binder_abs_receive_tr' @{const_syntax receive} @{syntax_const "_receive"}]
\<close>

(* FIXME: Mention that \<open>\<circ>\<close> binds stronger than all the above operators and binders. *)

lemma process_family_distinctnesses [induct_simp, simp]:
  shows
    "\<zero> \<noteq> A \<triangleleft> X"
  and
    "A \<triangleleft> X \<noteq> \<zero>"
  and
    "\<zero> \<noteq> A \<triangleright> x. \<P> x"
  and
    "A \<triangleright> x. \<P> x \<noteq> \<zero>"
  and
    "\<zero> \<noteq> P \<parallel> Q"
  and
    "P \<parallel> Q \<noteq> \<zero>"
  and
    "\<zero> \<noteq> \<nu> a. \<Q> a"
  and
    "\<nu> a. \<Q> a \<noteq> \<zero>"
  and
    "A \<triangleleft> X \<noteq> B \<triangleright> x. \<P> x"
  and
    "A \<triangleright> x. \<P> x \<noteq> B \<triangleleft> X"
  and
    "A \<triangleleft> X \<noteq> P \<parallel> Q"
  and
    "P \<parallel> Q \<noteq> A \<triangleleft> X"
  and
    "A \<triangleleft> X \<noteq> \<nu> a. \<Q> a"
  and
    "\<nu> a. \<Q> a \<noteq> A \<triangleleft> X"
  and
    "A \<triangleright> x. \<P> x \<noteq> P \<parallel> Q"
  and
    "P \<parallel> Q \<noteq> A \<triangleright> x. \<P> x"
  and
    "A \<triangleright> x. \<P> x \<noteq> \<nu> a. \<Q> a"
  and
    "\<nu> a. \<Q> a \<noteq> A \<triangleright> x. \<P> x"
  and
    "P \<parallel> Q \<noteq> \<nu> a. \<Q> a"
  and
    "\<nu> a. \<Q> a \<noteq> P \<parallel> Q"
  by (auto dest: fun_cong)

text \<open>
  Note that the above injectivity staments are not exhaustive, as they do not cover process families
  that are exotic at the top level. Therefore, if such process families occur, they are of no help.
\<close>

lemma process_family_injectivities [induct_simp, iff]:
  shows
    "A\<^sub>1 \<triangleleft> X\<^sub>1 = A\<^sub>2 \<triangleleft> X\<^sub>2 \<longleftrightarrow> A\<^sub>1 = A\<^sub>2 \<and> X\<^sub>1 = X\<^sub>2"
  and
    "A\<^sub>1 \<triangleright> x. \<P>\<^sub>1 x = A\<^sub>2 \<triangleright> x. \<P>\<^sub>2 x \<longleftrightarrow> A\<^sub>1 = A\<^sub>2 \<and> \<P>\<^sub>1 = \<P>\<^sub>2"
  and
    "P\<^sub>1 \<parallel> Q\<^sub>1 = P\<^sub>2 \<parallel> Q\<^sub>2 \<longleftrightarrow> P\<^sub>1 = P\<^sub>2 \<and> Q\<^sub>1 = Q\<^sub>2"
  and
    "\<nu> a. \<Q>\<^sub>1 a = \<nu> a. \<Q>\<^sub>2 a \<longleftrightarrow> \<Q>\<^sub>1 = \<Q>\<^sub>2"
  by (fastforce dest: fun_cong)+

lemma adapted_after_stop [simp]:
  shows "\<zero> \<guillemotleft> \<E> = \<zero>"
  by transfer (simp add: comp_def)

lemma adapted_after_send [simp]:
  shows "(A \<triangleleft> X) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<triangleleft> X \<guillemotleft> \<E>"
  by transfer (simp add: comp_def)

lemma adapted_after_receive [simp]:
  shows "(A \<triangleright> x. \<P> x) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<triangleright> x. \<P> x \<guillemotleft> \<E>"
  by transfer (simp add: comp_def)

lemma adapted_after_parallel [simp]:
  shows "(P \<parallel> Q) \<guillemotleft> \<E> = P \<guillemotleft> \<E> \<parallel> Q \<guillemotleft> \<E>"
  by transfer (simp add: comp_def)

lemma adapted_after_new_channel [simp]:
  shows "(\<nu> a. \<Q> a) \<guillemotleft> \<E> = \<nu> a. \<Q> a \<guillemotleft> \<E>"
  by (transfer, simp add: comp_def)

text \<open>
  The next set of lemmas states that a process that can be constructed both via a lifted data
  constructor and via adaptation can be constructed by applying the lifted data constructor to
  adaptations and also by adapting an application of the lifted data constructor.
\<close>
(* FIXME:
  \<^item> Check whether ``lifted data constructor'' is the right term (it sounds bulky).

  \<^item> Phrase this whole text in a more crisp way.

  \<^item> Rename the lemmas below to reflect the pattern described above.
*)

lemma stop_and_adapted:
  assumes "\<zero> = S \<guillemotleft> \<E>"
  shows "S = \<zero>"
  using adapted_undo and assms
  by (metis comp_def)

lemma send_and_adapted:
  assumes "A' \<triangleleft> X' = S \<guillemotleft> \<E>"
  obtains A and X where "A' = A \<guillemotleft> \<E>" and "X' = X \<guillemotleft> \<E>" and "S = A \<triangleleft> X"
proof -
  from assms have S_definition: "S = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<triangleleft> X' \<circ> inv \<lfloor>\<E>\<rfloor>"
    using adapted_undo
    by (metis comp_def)
  moreover
  from assms [symmetric] and S_definition have "A' = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>" and "X' = X' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>"
    by (simp_all del: comp_apply)
  ultimately show ?thesis
    using that
    by simp
qed

lemma receive_and_adapted:
  assumes "A' \<triangleright> x. \<P>' x = S \<guillemotleft> \<E>"
  obtains A and \<P> where "A' = A \<guillemotleft> \<E>" and "\<P>' = (\<lambda>x. \<P> x \<guillemotleft> \<E>)" and "S = A \<triangleright> x. \<P> x"
proof -
  have "S = S \<guillemotleft> \<E> \<circ> inv \<lfloor>\<E>\<rfloor>"
    by (simp only: adapted_undo)
  also have "\<dots> = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<triangleright> x. \<P>' x \<circ> inv \<lfloor>\<E>\<rfloor>"
    by (simp only: comp_def assms [symmetric])
  finally have S_definition: "S = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<triangleright> x. \<P>' x \<circ> inv \<lfloor>\<E>\<rfloor>" .
  moreover
  from assms [symmetric] and S_definition
  have "A' = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>" and "\<P>' = (\<lambda>x. \<P>' x \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>)"
    by (simp_all del: comp_apply)
  ultimately show ?thesis
    using that [where \<P> = "\<lambda>x. \<P>' x \<circ> inv \<lfloor>\<E>\<rfloor>"]
    by blast
qed

lemma parallel_and_adapted:
  assumes "P' \<parallel> Q' = S \<guillemotleft> \<E>"
  obtains P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
proof -
  from assms have S_definition: "S = P' \<circ> inv \<lfloor>\<E>\<rfloor> \<parallel> Q' \<circ> inv \<lfloor>\<E>\<rfloor>"
    using adapted_undo
    by (metis comp_def)
  moreover
  from assms [symmetric] and S_definition have "P' = P' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>" and "Q' = Q' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>"
    by (simp_all del: comp_apply)
  ultimately show ?thesis
    using that
    by simp
qed

lemma new_channel_and_adapted:
  assumes "\<nu> a. \<P>' a = S \<guillemotleft> \<E>"
  obtains \<P> where "\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)" and "S = \<nu> a. \<P> a"
proof -
  have "S = S \<guillemotleft> \<E> \<circ> inv \<lfloor>\<E>\<rfloor>"
    by (simp only: adapted_undo)
  also have "\<dots> = \<nu> a. \<P>' a \<circ> inv \<lfloor>\<E>\<rfloor>"
    by (simp only: comp_def assms [symmetric])
  finally have S_definition: "S = \<nu> a. \<P>' a \<circ> inv \<lfloor>\<E>\<rfloor>" .
  moreover
  from assms [symmetric] and S_definition have "\<P>' = (\<lambda>a. \<P>' a \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>)"
    by (simp_all del: comp_apply)
  ultimately show ?thesis
    using that [where \<P> = "\<lambda>a. \<P>' a \<circ> inv \<lfloor>\<E>\<rfloor>"]
    by simp
qed

definition create_channel :: "process family \<Rightarrow> process family" (\<open>\<star>\<close>) where
  [simp]: "\<star> = new_channel \<circ> \<Delta>"

lemma adapted_after_create_channel:
  shows "\<star> P \<guillemotleft> \<E> = \<star> (P \<guillemotleft> on_tail \<E>)"
  unfolding on_tail_def
  by transfer (simp add: comp_def)

lemma adapted_after_create_channel_power:
  shows "\<star>\<^bsup>n\<^esup> P \<guillemotleft> \<E> = \<star>\<^bsup>n\<^esup> (P \<guillemotleft> on_suffix n \<E>)"
proof (induction n arbitrary: \<E>)
  case 0
  then show ?case
    by (simp add: identity_as_partial_on_suffix [symmetric])
next
  case (Suc n \<E>)
  show ?case
  proof -
    have "\<star>\<^bsup>Suc n\<^esup> P \<guillemotleft> \<E> = \<star> (\<star>\<^bsup>n\<^esup> P) \<guillemotleft> \<E>"
      by simp
    also have "\<dots> = \<star> (\<star>\<^bsup>n\<^esup> P \<guillemotleft> on_tail \<E>)"
      by (simp only: adapted_after_create_channel)
    also have "\<dots> = \<star> (\<star>\<^bsup>n\<^esup> (P \<guillemotleft> on_suffix n (on_tail \<E>)))"
      by (simp only: Suc.IH)
    also have "\<dots> = \<star> (\<star>\<^bsup>n\<^esup> (P \<guillemotleft> on_suffix (Suc n) \<E>))"
      unfolding on_tail_def
      using composition_as_partial_on_suffix [THEN fun_cong]
      by simp
    also have "\<dots> = \<star>\<^bsup>Suc n\<^esup> (P \<guillemotleft> on_suffix (Suc n) \<E>)"
      by simp
    finally show ?thesis .
  qed
qed

text \<open>
  We define guarding of processes at the host-language level.
\<close>

definition guard :: "bool \<Rightarrow> process family \<Rightarrow> process family" (infixr \<open>?\<close> 52) where
  [simp]: "x ? P = (if x then P else \<zero>)"

text \<open>
  We define parallel composition over a list of processes families.
\<close>

primrec general_parallel :: "('a \<Rightarrow> process family) \<Rightarrow> 'a list \<Rightarrow> process family" where
  "general_parallel _ [] = \<zero>" |
  "general_parallel f (x # xs) = f x \<parallel> general_parallel f xs"

text \<open>
  We define a notation for repeated parallel composition combined with mapping. Since this notation
  clashes with \<open>HOL.Groups_List._prod_list\<close>, we have to remove the latter.
\<close>

no_syntax
  "_prod_list" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" (\<open>(3\<Prod>_\<leftarrow>_. _)\<close> [0, 51, 10] 10)
syntax
  "_general_parallel" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> process \<Rightarrow> process" (\<open>(3\<Prod>_\<leftarrow>_. _)\<close> [0, 0, 52] 52)
translations
  "\<Prod>x\<leftarrow>xs. P" \<rightleftharpoons> "CONST general_parallel (\<lambda>x. P) xs"
print_translation \<open>
  [
    preserve_binder_abs_general_parallel_tr'
      @{const_syntax general_parallel}
      @{syntax_const "_general_parallel"}
  ]
\<close>

lemma general_parallel_conversion_deferral:
  shows "\<Prod>y \<leftarrow> map f xs. \<P> y = \<Prod>x \<leftarrow> xs. \<P> (f x)"
  by (induction xs) simp_all

end
