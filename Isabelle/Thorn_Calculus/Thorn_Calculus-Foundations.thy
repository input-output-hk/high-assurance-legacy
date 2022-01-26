section \<open>Foundations\<close>

theory "Thorn_Calculus-Foundations"
imports
  Main
  "HOL-Library.Stream"
begin

(* FIXME: Document the following at an appropriate place:

    \<^item> We use families for channels, because we need transitions to be homogeneous in channels. On
      the other hand, transitions must be able to be inhomogeneous in values in order to allow for
      computation, and thus we do not use families for values.

    \<^item> Environments are the HOAS-equivalent of assignments of channels to names. Families are then
      the HOAS analog of processes with free channel names.

    \<^item> The name introduced by a \<open>\<nu>\<close>-binder corresponds to the first element of an environment. All
      previous elements are shifted forward by one index. Thus the indexes of the elements of an
      environment correspond to the de~Bruijn indexes of the names.

    \<^item> We define environments as infinite lists, because we cannot track the lengths of finite
      channel lists using the type system, as Isabelle/HOL does not support dependent types nor
      heterogeneous inductive predicates (which would require higher-rank polymorphism). In
      practice we always deal with families that only depend on a finite prefix of the environment,
      but all the meta-theory works out without imposing such a restriction.
*)

(* FIXME:
  Maybe we should not have the policy of proving only those lemmas that we use later or which are of
  obvious use for other sessions. In particular, it might be good to include lemmas that are
  analogous to existing lemmas, like \<open>\<Delta>\<close>-counterparts of \<open>\<nabla>\<close>-lemmas or counterparts of process
  constructor lemmas for different process constructors.
*)

subsection \<open>Channels and Values\<close>

typedecl chan

axiomatization where
  more_than_one_chan:
    "\<exists>a b :: chan. a \<noteq> b"

typedecl val

subsection \<open>Environments\<close>

type_synonym environment = "chan stream"

text \<open>
  Regarding the naming, note that \<^const>\<open>insert\<close> is already taken. For adaptations, we do not use
  the \<open>_at\<close> suffix and thus have \<open>remove\<close> as the equivalent of \<open>delete_at\<close>.
\<close>

definition insert_at :: "nat \<Rightarrow> chan \<Rightarrow> environment \<Rightarrow> environment" where
  [simp]: "insert_at i a e = stake i e @- a ## sdrop i e"

definition delete_at :: "nat \<Rightarrow> environment \<Rightarrow> environment" where
  [simp]: "delete_at i e = stake i e @- sdrop (Suc i) e"

lemma insert_at_after_delete_at:
  shows "insert_at i (e !! i) (delete_at i e) = e"
  by (simp del: sdrop.simps(2) add: stake_shift sdrop_shift id_stake_snth_sdrop [symmetric])

lemma delete_at_after_insert_at:
  shows "delete_at i (insert_at i a e) = e"
  by (simp add: stake_append sdrop_shift stake_sdrop)

subsection \<open>Families\<close>

type_synonym 'a family = "environment \<Rightarrow> 'a"

definition constant_family :: "'a \<Rightarrow> 'a family" (\<open>\<box>\<close>) where
  [simp]: "\<box> v = (\<lambda>_. v)"

subsection \<open>Adaptations\<close>

typedef adaptation = "{E :: environment \<Rightarrow> environment. surj E}"
  by auto

text \<open>
  Surjectivity is needed for the following:

    \<^item> \<^theory_text>\<open>adapted_injectivity\<close>, used here:

        \<^item> Pre-simplification in proofs with concrete process families (well, the adaptations used in
          the transition system \<^emph>\<open>are\<close> surjective; the above surjectivity requirement just kind of
          centralizes the handling of the surjectivity of all of them

        \<^item> Handling of the ``non-constant'' requirement of the \<^theory_text>\<open>opening\<close> rule in that lemma on
          equivalence of transitions with transitions containing adaption

    \<^item> Deriving of the backward implication from the forward implication in the above-mentioned
      lemma
\<close>
(* FIXME: Check if there are more. *)

notation Rep_adaptation (\<open>(\<lfloor>_\<rfloor>)\<close>)

setup_lifting type_definition_adaptation

lift_definition adaptation_identity :: adaptation (\<open>\<one>\<close>)
  is id
  using surj_id .

lift_definition adaptation_composition :: "adaptation \<Rightarrow> adaptation \<Rightarrow> adaptation" (infixl "\<bullet>" 55)
  is "(\<circ>)"
  using comp_surj .

lemma adaptation_composition_associativity:
  shows "(\<E> \<bullet> \<D>) \<bullet> \<C> = \<E> \<bullet> (\<D> \<bullet> \<C>)"
  by transfer (rule comp_assoc)

lemma adaptation_composition_left_identity:
  shows "\<one> \<bullet> \<E> = \<E>"
  by transfer simp

lemma adaptation_composition_right_identity:
  shows "\<E> \<bullet> \<one> = \<E>"
  by transfer simp

lift_definition adapted :: "'a family \<Rightarrow> adaptation \<Rightarrow> 'a family" (infixl "\<guillemotleft>" 55)
  is "(\<circ>)" .

lemma identity_adapted:
  shows "V \<guillemotleft> \<one> = V"
  by transfer simp

lemma composition_adapted:
  shows "V \<guillemotleft> (\<E> \<bullet> \<D>) = V \<guillemotleft> \<E> \<guillemotleft> \<D>"
  by transfer (simp add: comp_assoc)

lemma adapted_undo:
  shows "V \<guillemotleft> \<E> \<circ> inv \<lfloor>\<E>\<rfloor> = V"
  by transfer (simp add: comp_assoc surj_iff)

text \<open>
  The following is not just a pre-simplification rules but a very important law, used as a
  simplification rule in several places. See above for the arguments in favor of surjectivity.
\<close>

lemma adapted_injectivity [induct_simp, iff]:
  shows "V \<guillemotleft> \<E> = W \<guillemotleft> \<E> \<longleftrightarrow> V = W"
proof
  assume "V \<guillemotleft> \<E> = W \<guillemotleft> \<E>"
  then have "V \<guillemotleft> \<E> \<circ> inv \<lfloor>\<E>\<rfloor> = W \<guillemotleft> \<E> \<circ> inv \<lfloor>\<E>\<rfloor>"
    by simp
  then show "V = W"
    unfolding adapted_undo .
next
  assume "V = W"
  then show "V \<guillemotleft> \<E> = W \<guillemotleft> \<E>"
    by simp
qed

subsubsection \<open>Injective Adaptations\<close>

lift_definition injective :: "adaptation \<Rightarrow> bool"
  is inj .

lemma injective_introduction:
  assumes "\<D> \<bullet> \<E> = \<one>"
  shows "injective \<E>"
  using assms
  by transfer (metis inj_on_id inj_on_imageI2)

text \<open>
  The following elimination rule captures two important properties:

    \<^item> The left inverse of an injective adaptation is surjective and thus and adaptation itself.

    \<^item> The left inverse of an injective adaptation is also a right inverse.
\<close>

lemma injective_elimination:
  assumes "injective \<E>"
  obtains \<D> where "\<D> \<bullet> \<E> = \<one>" and "\<E> \<bullet> \<D> = \<one>"
proof -
  from \<open>injective \<E>\<close> have "bijection \<lfloor>\<E>\<rfloor>"
    unfolding bijection_def
    by transfer (rule bijI)
  then have "surj (inv \<lfloor>\<E>\<rfloor>)" and "inv \<lfloor>\<E>\<rfloor> \<circ> \<lfloor>\<E>\<rfloor> = id" and "\<lfloor>\<E>\<rfloor> \<circ> inv \<lfloor>\<E>\<rfloor> = id"
    by (fact bijection.surj_inv, fact bijection.inv_comp_left, fact bijection.inv_comp_right)
  with that show ?thesis
    by transfer simp 
qed

lemma identity_is_injective:
  shows "injective \<one>"
  by transfer simp

lemma composition_is_injective:
  assumes "injective \<E>" and "injective \<D>"
  shows "injective (\<E> \<bullet> \<D>)"
  using assms
  by transfer (rule inj_compose)

subsubsection \<open>Working with Suffixes\<close>

lift_definition suffix :: "nat \<Rightarrow> adaptation"
  is sdrop
proof (rule surjI)
  fix n and e'
  show "sdrop n (replicate n undefined @- e') = e'"
    by (simp add: sdrop_shift)
qed

definition tail :: adaptation where
  [simp]: "tail = suffix 1"

lift_definition on_suffix :: "nat \<Rightarrow> adaptation \<Rightarrow> adaptation"
  is "\<lambda>n E. \<lambda>e. stake n e @- E (sdrop n e)"
proof (rule surjI)
  fix n and E :: "environment \<Rightarrow> environment" and e'
  assume "surj E"
  then show "(\<lambda>e. stake n e @- E (sdrop n e)) (stake n e' @- inv E (sdrop n e')) = e'"
    by (simp add: stake_shift sdrop_shift surj_f_inv_f stake_sdrop)
qed

definition on_tail :: "adaptation \<Rightarrow> adaptation" where
  [simp]: "on_tail = on_suffix 1"

lemma identity_as_on_suffix:
  shows "\<one> = on_suffix n \<one>"
  by transfer (auto simp add: stake_sdrop)

lemma composition_as_on_suffix:
  shows "on_suffix n \<E> \<bullet> on_suffix n \<D> = on_suffix n (\<E> \<bullet> \<D>)"
  by transfer (simp add: comp_def stake_shift sdrop_shift)

lemma identity_as_partial_on_suffix:
  shows "id = on_suffix 0"
  by (rule ext, transfer) simp

lemma composition_as_partial_on_suffix:
  shows "on_suffix n \<circ> on_suffix m = on_suffix (n + m)"
  by (rule ext, transfer) (simp del: shift_append add: shift_append [symmetric])

lemma on_suffix_is_injective:
  assumes "injective \<E>"
  shows "injective (on_suffix n \<E>)"
proof -
  from \<open>injective \<E>\<close> obtain \<D> where "\<D> \<bullet> \<E> = \<one>"
    by (blast elim: injective_elimination)
  have "on_suffix n \<D> \<bullet> on_suffix n \<E> = on_suffix n (\<D> \<bullet> \<E>)"
    by transfer (simp add: comp_def stake_shift sdrop_shift)
  also have "\<dots> = on_suffix n \<one>"
    using \<open>\<D> \<bullet> \<E> = \<one>\<close>
    by simp
  also have "\<dots> = \<one>"
    using identity_as_on_suffix [symmetric] .
  finally show ?thesis
    by (fact injective_introduction)
qed

lemma suffix_after_on_suffix:
  shows "suffix n \<bullet> on_suffix n \<E> = \<E> \<bullet> suffix n"
  by transfer (simp add: comp_def sdrop_shift)

lemma suffix_adapted_and_on_suffix_adapted:
  assumes "V' \<guillemotleft> suffix n = W \<guillemotleft> on_suffix n \<E>"
  obtains V where "V' = V \<guillemotleft> \<E>" and "W = V \<guillemotleft> suffix n"
proof -
  have V'_definition: "V' = W \<circ> (\<lambda>e. replicate n undefined @- e) \<guillemotleft> \<E>"
  proof -
    have "V' = V' \<guillemotleft> suffix n \<circ> (\<lambda>e. replicate n undefined @- e)"
      by transfer (simp add: comp_def sdrop_shift)
    also have "\<dots> = W \<guillemotleft> on_suffix n \<E> \<circ> (\<lambda>e. replicate n undefined @- e)"
      by (simp only: assms)
    also have "\<dots> = W \<circ> (\<lambda>e. replicate n undefined @- e) \<guillemotleft> \<E>"
      by transfer (simp add: comp_def stake_shift sdrop_shift)
    finally show ?thesis.
  qed
  moreover
  have "W = W \<circ> (\<lambda>e. replicate n undefined @- e) \<guillemotleft> suffix n"
  proof -
    have "
      W \<circ> (\<lambda>e. replicate n undefined @- e) \<guillemotleft> suffix n \<guillemotleft> on_suffix n \<E>
      =
      W \<circ> (\<lambda>e. replicate n undefined @- e) \<guillemotleft> \<E> \<guillemotleft> suffix n"
      by transfer (simp_all add: comp_def sdrop_shift)
    also have "\<dots> = W \<guillemotleft> on_suffix n \<E>"
      using assms unfolding V'_definition . 
    finally show ?thesis
      by simp
  qed
  ultimately show ?thesis
    using that
    by blast
qed

subsubsection \<open>Working with Elements\<close>

lift_definition remove :: "nat \<Rightarrow> adaptation"
  is delete_at
proof (rule surjI)
  fix n and e'
  show "delete_at n (insert_at n undefined e') = e'"
    using delete_at_after_insert_at .
qed

lift_definition move :: "nat \<Rightarrow> nat \<Rightarrow> adaptation"
  is "\<lambda>i j. \<lambda>e. insert_at j (e !! i) (delete_at i e)"
proof (rule surjI)
  fix i and j and e'
  show "(\<lambda>e. insert_at j (e !! i) (delete_at i e)) (insert_at i (e' !! j) (delete_at j e')) = e'"
    \<comment> \<open>This is essentially the statement of \<^theory_text>\<open>back_and_forth_moves\<close> below.\<close>
    using delete_at_after_insert_at and insert_at_after_delete_at
    by simp
qed

lemma identity_as_move:
  shows "\<one> = move i i"
  using insert_at_after_delete_at
  by transfer (simp add: id_def)

lemma composition_as_move:
  shows "move j k \<bullet> move i j = move i k"
  using delete_at_after_insert_at
  by transfer auto

lemma back_and_forth_moves:
  shows "move j i \<bullet> move i j = \<one>"
  using composition_as_move and identity_as_move [symmetric]
  by simp

lemma move_is_injective:
  shows "injective (move i j)"
  using back_and_forth_moves
  by (rule injective_introduction)

lemma on_suffix_remove:
  shows "on_suffix n (remove i) = remove (n + i)"
  by transfer (auto simp del: shift_append simp add: shift_append [symmetric])

lemma on_suffix_move:
  shows "on_suffix n (move i j) = move (n + i) (n + j)"
  by
    transfer
    (simp
      del: stake_add sdrop_add
      add: stake_add [symmetric] sdrop_add [symmetric] stake_shift sdrop_shift sdrop_snth
    )

lemma remove_after_suffix:
  shows "remove i \<bullet> suffix n = suffix n \<bullet> remove (n + i)"
  by transfer (simp add: comp_def sdrop_shift drop_stake)

lemma move_after_suffix:
  shows "move i j \<bullet> suffix n = suffix n \<bullet> move (n + i) (n + j)"
  by
    (transfer fixing: i j, cases "i < j")
    (simp_all
      add: comp_def stake_shift sdrop_shift take_stake drop_stake min_absorb2 min_absorb1 sdrop_snth
    )

lemma suffix_after_remove:
  assumes "i \<le> n"
  shows "suffix n \<bullet> remove i = suffix (Suc n)"
  using assms
  by transfer (auto simp add: sdrop_shift)

context begin

private lemma suffix_after_move_away_from_front:
  assumes "i \<le> j" and "j < n"
  shows "suffix n \<bullet> move i j = suffix n"
proof -
  from \<open>j < n\<close> obtain m where "n = Suc m" and "j \<le> m"
    by (auto elim: lessE)
  from \<open>i \<le> j\<close> and \<open>j \<le> m\<close> show ?thesis
    unfolding \<open>n = Suc m\<close>
    by transfer (auto simp add: sdrop_shift Suc_diff_le)
qed

lemma suffix_after_move:
  assumes "i < n" and "j < n"
  shows "suffix n \<bullet> move i j = suffix n"
proof (cases "i \<le> j")
  case True
  with \<open>j < n\<close> show ?thesis
    by (intro suffix_after_move_away_from_front)
next
  case False
  with \<open>i < n\<close> have "suffix n \<bullet> move i j = (suffix n \<bullet> move j i) \<bullet> move i j"
    by (simp only: suffix_after_move_away_from_front)
  also have "\<dots> = suffix n"
    by
      (simp only:
        adaptation_composition_associativity
        back_and_forth_moves
        adaptation_composition_right_identity
      )
  finally show ?thesis .
qed

end

lemma remove_after_on_suffix:
  assumes "i \<le> n"
  shows "remove i \<bullet> on_suffix (Suc n) \<E> = on_suffix n \<E> \<bullet> remove i"
  using assms
  by
    transfer
    (simp
      del: stake.simps(2)
      add: comp_def stake_shift sdrop_shift take_stake drop_stake min_absorb1 min_absorb2
    )

context begin

private definition finite_insert_at :: "nat \<Rightarrow> chan \<Rightarrow> chan list \<Rightarrow> chan list" where
  [simp]: "finite_insert_at i a e = take i e @ a # drop i e"

private definition finite_delete_at :: "nat \<Rightarrow> chan list \<Rightarrow> chan list" where
  [simp]: "finite_delete_at i e = take i e @ drop (Suc i) e"

lemma move_after_on_suffix:
  assumes "i < n" and "j < n"
  shows "move i j \<bullet> on_suffix n \<E> = on_suffix n \<E> \<bullet> move i j"
proof -
  have "
    (\<lambda>e'. insert_at j (e' !! i) (delete_at i e')) (stake n e @- E (sdrop n e)) =
    (\<lambda>e'. stake n e' @- E (sdrop n e')) (insert_at j (e !! i) (delete_at i e))"
    (is "?e\<^sub>1 = ?e\<^sub>2")
    for E and e
  proof -
    \<comment> \<open>Turn \<^term>\<open>e' !! i\<close> into \<^term>\<open>e !! i\<close>:\<close>
    have "?e\<^sub>1 = insert_at j (e !! i) (delete_at i (stake n e @- E (sdrop n e)))"
      using \<open>i < n\<close>
      by simp
    \<comment> \<open>Push deletion and insertion into the prefix argument of \<^term>\<open>(@-)\<close>:\<close>
    also have "\<dots> = insert_at j (e !! i) (finite_delete_at i (stake n e) @- E (sdrop n e))"
      using \<open>i < n\<close>
      by (simp add: stake_shift sdrop_shift)
    also have "\<dots> = finite_insert_at j (e !! i) (finite_delete_at i (stake n e)) @- E (sdrop n e)"
      using \<open>j < n\<close>
      by (simp add: stake_shift sdrop_shift)
    \<comment> \<open>Push deletion and insertion into the stream argument of \<^const>\<open>stake\<close>:\<close>
    also note stake_push_rules = take_stake drop_stake stake_shift min_absorb1 min_absorb2
    have "\<dots> = finite_insert_at j (e !! i) (stake (n - 1) (delete_at i e)) @- E (sdrop n e)"
      using \<open>i < n\<close>
      by (simp add: stake_push_rules)
    also have "\<dots> = stake n (insert_at j (e !! i) (delete_at i e)) @- E (sdrop n e)"
      using \<open>j < n\<close>
      by (simp del: delete_at_def add: stake_push_rules Suc_diff_Suc [symmetric])
    \<comment> \<open>Turn \<^term>\<open>sdrop n e\<close> into \<^term>\<open>sdrop n e'\<close>:\<close>
    also have "\<dots> =
      stake n (insert_at j (e !! i) (delete_at i e)) @- E (sdrop (n - 1) (delete_at i e))"
      using \<open>i < n\<close>
      by (simp del: sdrop.simps(2) add: sdrop_shift drop_stake)
    also have "\<dots> = ?e\<^sub>2"
      using \<open>j < n\<close>
      by (simp del: delete_at_def add: sdrop_shift drop_stake Suc_diff_Suc [symmetric])
    \<comment> \<open>Put everything together:\<close>
    finally show ?thesis .
  qed
  then show ?thesis
    by transfer auto
qed

end

lemma move_adapted_and_on_suffix_adapted:
  assumes "i < n" and "j < n" and "V' \<guillemotleft> move i j = W \<guillemotleft> on_suffix n \<E>"
  obtains V where "V' = V \<guillemotleft> on_suffix n \<E>" and "W = V \<guillemotleft> move i j"
proof -
  have "V' = W \<guillemotleft> move j i \<guillemotleft> on_suffix n \<E>"
  proof -
    have "V' = V' \<guillemotleft> move i j \<guillemotleft> move j i"
      by (simp only: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
    also have "\<dots> = W \<guillemotleft> on_suffix n \<E> \<guillemotleft> move j i"
      using \<open>V' \<guillemotleft> move i j = W \<guillemotleft> on_suffix n \<E>\<close>
      by simp
    also have "\<dots> = W \<guillemotleft> move j i \<guillemotleft> on_suffix n \<E>"
      using \<open>i < n\<close> and \<open>j < n\<close>
      by (simp only: composition_adapted [symmetric] move_after_on_suffix)
    finally show ?thesis .
  qed
  moreover have "W = W \<guillemotleft> move j i \<guillemotleft> move i j"
    by (simp only: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
  ultimately show ?thesis
    using that
    by blast
qed

lemma remove_adapted_and_on_suffix_adapted:
  assumes "i \<le> n" and "V' \<guillemotleft> remove i = W \<guillemotleft> on_suffix (Suc n) \<E>"
  obtains V where "V' = V \<guillemotleft> on_suffix n \<E>" and "W = V \<guillemotleft> remove i"
proof -
  from assms(2) have "V' \<guillemotleft> tail \<guillemotleft> move i 0 = W \<guillemotleft> on_suffix (Suc n) \<E>"
    unfolding tail_def
    by transfer (simp add: comp_def)
  then obtain V'' where "V' \<guillemotleft> tail = V'' \<guillemotleft> on_suffix (Suc n) \<E>" and "W = V'' \<guillemotleft> move i 0"
    using move_adapted_and_on_suffix_adapted [OF le_imp_less_Suc [OF \<open>i \<le> n\<close>]]
    by blast
  from this(1) have "V' \<guillemotleft> tail = V'' \<guillemotleft> on_tail (on_suffix n \<E>)"
    using composition_as_partial_on_suffix [THEN fun_cong]
    by simp
  then obtain V where "V' = V \<guillemotleft> on_suffix n \<E>" and "V'' = V \<guillemotleft> tail"
    unfolding tail_def and on_tail_def
    using suffix_adapted_and_on_suffix_adapted
    by blast
  from \<open>W = V'' \<guillemotleft> move i 0\<close> and \<open>V'' = V \<guillemotleft> tail\<close> have "W = V \<guillemotleft> remove i"
    unfolding tail_def
    by transfer (simp add: comp_def)
  with that and \<open>V' = V \<guillemotleft> on_suffix n \<E>\<close> show ?thesis .
qed

lemma remove_after_move:
  shows "remove j \<bullet> move i j = remove i"
  using delete_at_after_insert_at
  by transfer auto

lemma move_after_backyard_remove:
  assumes "j < i" and "k < i"
  shows "move j k \<bullet> remove i = remove i \<bullet> move j k"
proof -
  have "move j k \<bullet> remove i = move j k \<bullet> on_suffix i (remove 0)"
    by (simp add: on_suffix_remove)
  also have "\<dots> = on_suffix i (remove 0) \<bullet> move j k"
    using assms
    by (simp only: move_after_on_suffix)
  also have "\<dots> = remove i \<bullet> move j k"
    by (simp add: on_suffix_remove)
  finally show ?thesis .
qed

lemma move_after_backyard_move:
  assumes "k < i" and "k < j" and "l < i" and "l < j"
  shows "move k l \<bullet> move i j = move i j \<bullet> move k l"
proof -
  have "move k l \<bullet> move i j = move k l \<bullet> on_suffix (min i j) (move (i - min i j) (j - min i j))"
    by (simp add: on_suffix_move)
  also have "\<dots> = on_suffix (min i j) (move (i - min i j) (j - min i j)) \<bullet> move k l"
    using assms
    by (simp only: move_after_on_suffix)
  also have "\<dots> = move i j \<bullet> move k l"
    by (simp add: on_suffix_move)
  finally show ?thesis .
qed

lemma neighbor_commutation:
  shows "move i (Suc i) = move (Suc i) i"
proof -
  have "move 0 1 = move 1 0"
    by transfer simp
  then have "on_suffix i (move 0 1) = on_suffix i (move 1 0)"
    by simp
  then show ?thesis
    by (simp add: on_suffix_move)
qed

context begin

private lemma neighbor_commutation_after_tight_outer_move_away_from_front:
  shows "move i (Suc i) \<bullet> move i (Suc (Suc i)) = move i (Suc (Suc i)) \<bullet> move (Suc i) (Suc (Suc i))"
proof -
  have "move 0 1 \<bullet> move 0 2 = move 0 2 \<bullet> move 1 2"
    by transfer (simp add: comp_def numeral_2_eq_2)
  then have "on_suffix i (move 0 1 \<bullet> move 0 2) = on_suffix i (move 0 2 \<bullet> move 1 2)"
    by simp
  then show ?thesis
    by (simp add: composition_as_on_suffix [symmetric] on_suffix_move)
qed

private lemma neighbor_commutation_after_outer_move_away_from_front:
  assumes "i \<le> k" and "Suc k < j"
  shows "move k (Suc k) \<bullet> move i j = move i j \<bullet> move (Suc k) (Suc (Suc k))"
proof -
  have "
    move k (Suc k) \<bullet> move i j
    =
    move k (Suc k) \<bullet> (move (Suc (Suc k)) j \<bullet> move k (Suc (Suc k)) \<bullet> move i k)"
    by (simp only: composition_as_move)
  also have "\<dots> = (move k (Suc k) \<bullet> move (Suc (Suc k)) j) \<bullet> move k (Suc (Suc k)) \<bullet> move i k"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = (move (Suc (Suc k)) j \<bullet> move k (Suc k)) \<bullet> move k (Suc (Suc k)) \<bullet> move i k"
    using move_after_backyard_move and \<open>Suc k < j\<close>
    by (metis lessI Suc_lessD)
  also have "\<dots> = move (Suc (Suc k)) j \<bullet> (move k (Suc k) \<bullet> move k (Suc (Suc k))) \<bullet> move i k"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move (Suc (Suc k)) j \<bullet> (move k (Suc (Suc k)) \<bullet> move (Suc k) (Suc (Suc k))) \<bullet> move i k"
    by (simp only: neighbor_commutation_after_tight_outer_move_away_from_front)
  also have "\<dots> = move (Suc (Suc k)) j \<bullet> move k (Suc (Suc k)) \<bullet> (move (Suc k) (Suc (Suc k)) \<bullet> move i k)"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move (Suc (Suc k)) j \<bullet> move k (Suc (Suc k)) \<bullet> (move i k \<bullet> move (Suc k) (Suc (Suc k)))"
    using move_after_backyard_move and \<open>i \<le> k\<close>
    by (metis less_Suc_eq le_imp_less_Suc)
  also have "\<dots> = (move (Suc (Suc k)) j \<bullet> move k (Suc (Suc k)) \<bullet> move i k) \<bullet> move (Suc k) (Suc (Suc k))"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move i j \<bullet> move (Suc k) (Suc (Suc k))"
    by (simp only: composition_as_move)
  finally show ?thesis .
qed

private lemma move_away_from_front_after_outer_move_away_from_front:
  assumes "i \<le> k" and "k \<le> l" and "l < j"
  shows "move k l \<bullet> move i j = move i j \<bullet> move (Suc k) (Suc l)"
using \<open>k \<le> l\<close> proof (induction rule: dec_induct)
  case base
  then show ?case
    by
      (simp only:
        identity_as_move [symmetric]
        adaptation_composition_left_identity
        adaptation_composition_right_identity
      )
next
  case (step m)
  have "move k (Suc m) \<bullet> move i j = (move m (Suc m) \<bullet> move k m) \<bullet> move i j"
    by (simp only: composition_as_move)
  also have "\<dots> = move m (Suc m) \<bullet> (move k m \<bullet> move i j)"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move m (Suc m) \<bullet> (move i j \<bullet> move (Suc k) (Suc m))"
    by (simp only: step.IH)
  also have "\<dots> = (move m (Suc m) \<bullet> move i j) \<bullet> move (Suc k) (Suc m)"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = (move i j \<bullet> move (Suc m) (Suc (Suc m))) \<bullet> move (Suc k) (Suc m)"
    using \<open>i \<le> k\<close> and \<open>l < j\<close> and \<open>k \<le> m\<close> and \<open>m < l\<close>
    by (simp only: neighbor_commutation_after_outer_move_away_from_front)
  also have "\<dots> = move i j \<bullet> (move (Suc m) (Suc (Suc m)) \<bullet> move (Suc k) (Suc m))"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move i j \<bullet> move (Suc k) (Suc (Suc m))"
    by (simp only: composition_as_move)
  finally show ?case .
qed

lemma move_after_outer_move_away_from_front:
  assumes "i \<le> k" and "i \<le> l" and "k < j" and "l < j"
  shows "move k l \<bullet> move i j = move i j \<bullet> move (Suc k) (Suc l)"
proof (cases "k \<le> l")
  case True
  with \<open>i \<le> k\<close> and \<open>l < j\<close> show ?thesis
    by (intro move_away_from_front_after_outer_move_away_from_front)
next
  case False
  have "move k l \<bullet> move i j = move k l \<bullet> move i j \<bullet> (move (Suc l) (Suc k) \<bullet> move (Suc k) (Suc l))"
    by (simp only: back_and_forth_moves adaptation_composition_right_identity)
  also have "\<dots> = move k l \<bullet> (move i j \<bullet> move (Suc l) (Suc k)) \<bullet> move (Suc k) (Suc l)"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move k l \<bullet> (move l k \<bullet> move i j) \<bullet> move (Suc k) (Suc l)"
    using \<open>i \<le> l\<close> and \<open>k < j\<close> and \<open>\<not> k \<le> l\<close>
    by (simp only: move_away_from_front_after_outer_move_away_from_front)
  also have "\<dots> = (move k l \<bullet> move l k) \<bullet> move i j \<bullet> move (Suc k) (Suc l)"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move i j \<bullet> move (Suc k) (Suc l)"
    by (simp only: back_and_forth_moves adaptation_composition_left_identity)
  finally show ?thesis .
qed

end

lemma outer_move_towards_front_after_move:
  assumes "i \<le> k" and "i \<le> l" and "k < j" and "l < j"
  shows "move j i \<bullet> move k l = move (Suc k) (Suc l) \<bullet> move j i"
proof -
  have "move j i \<bullet> move k l = move j i \<bullet> move k l \<bullet> (move i j \<bullet> move j i)"
    by (simp only: back_and_forth_moves adaptation_composition_right_identity)
  also have "\<dots> = move j i \<bullet> (move k l \<bullet> move i j) \<bullet> move j i"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move j i \<bullet> (move i j \<bullet> move (Suc k) (Suc l)) \<bullet> move j i"
    using \<open>i \<le> k\<close> and \<open>i \<le> l\<close> and \<open>k < j\<close> and \<open>l < j\<close>
    by (simp only: move_after_outer_move_away_from_front)
  also have "\<dots> = (move j i \<bullet> move i j) \<bullet> move (Suc k) (Suc l) \<bullet> move j i"
    by (simp only: adaptation_composition_associativity)
  also have "\<dots> = move (Suc k) (Suc l) \<bullet> move j i"
    by (simp only: back_and_forth_moves adaptation_composition_left_identity)
  finally show ?thesis .
qed

subsection \<open>Currying\<close>

definition family_curry :: "'a family \<Rightarrow> (chan \<Rightarrow> 'a family)" (\<open>\<Delta>\<close>) where
  [simp]: "\<Delta> V = (\<lambda>a. \<lambda>e. V (a ## e))"

definition family_uncurry :: "(chan \<Rightarrow> 'a family) \<Rightarrow> 'a family" (\<open>\<nabla>\<close>) where
  [simp]: "\<nabla> \<V> = (\<lambda>e. \<V> (shd e) (stl e))"

definition deep_curry :: "nat \<Rightarrow> 'a family \<Rightarrow> (chan \<Rightarrow> 'a family)" (\<open>(\<Delta>\<^bsub>_\<^esub>)\<close>) where
  [simp]: "\<Delta>\<^bsub>i\<^esub> V = (\<lambda>a. \<lambda>e. V (insert_at i a e))"

definition deep_uncurry :: "nat \<Rightarrow> (chan \<Rightarrow> 'a family) \<Rightarrow> 'a family" (\<open>(\<nabla>\<^bsub>_\<^esub>)\<close>) where
  [simp]: "\<nabla>\<^bsub>i\<^esub> \<V> = (\<lambda>e. \<V> (e !! i) (delete_at i e))"

lemma family_curry_is_bijective:
  shows "bij \<Delta>"
  by (rule o_bij [of \<nabla>]) auto

lemma family_uncurry_is_bijective:
  shows "bij \<nabla>"
  by (rule o_bij [of \<Delta>]) auto

lemma deep_curry_after_deep_uncurry:
  shows "\<Delta>\<^bsub>i\<^esub> \<circ> \<nabla>\<^bsub>i\<^esub> = id"
  by (rule ext) (simp del: sdrop.simps(2) add: stake_shift sdrop_shift, simp add: stake_sdrop)

lemma deep_uncurry_after_deep_curry:
  shows "\<nabla>\<^bsub>i\<^esub> \<circ> \<Delta>\<^bsub>i\<^esub> = id"
  by
    (rule ext)
    (simp del: sdrop.simps(2) add: stake_shift sdrop_shift id_stake_snth_sdrop [symmetric])

lemma deep_curry_is_bijective:
  shows "bij \<Delta>\<^bsub>i\<^esub>"
  using deep_uncurry_after_deep_curry and deep_curry_after_deep_uncurry
  by (rule o_bij [of "\<nabla>\<^bsub>i\<^esub>"])

lemma deep_uncurry_is_bijective:
  shows "bij \<nabla>\<^bsub>i\<^esub>"
  using deep_curry_after_deep_uncurry and deep_uncurry_after_deep_curry
  by (rule o_bij [of "\<Delta>\<^bsub>i\<^esub>"])

lemma family_curry_as_deep_curry:
  shows "\<Delta> V = \<Delta>\<^bsub>0\<^esub> V"
  by simp

lemma family_uncurry_as_deep_uncurry:
  shows "\<nabla> \<V> = \<nabla>\<^bsub>0\<^esub> \<V>"
  by simp

lemma family_curry_after_on_suffix_adapted:
  shows "\<Delta> (V \<guillemotleft> on_suffix (Suc n) \<E>) = (\<lambda>a. \<Delta> V a \<guillemotleft> on_suffix n \<E>)"
  by transfer (simp add: comp_def)

lemma on_suffix_adapted_after_family_uncurry:
  shows "\<nabla> \<V> \<guillemotleft> on_suffix (Suc n) \<E> = \<nabla> (\<lambda>a. \<V> a \<guillemotleft> on_suffix n \<E>)"
  by transfer (simp add: comp_def)

lemma deep_curry_after_on_suffix_adapted:
  assumes "i \<le> n"
  shows "\<Delta>\<^bsub>i\<^esub> (V \<guillemotleft> on_suffix (Suc n) \<E>) = (\<lambda>a. \<Delta>\<^bsub>i\<^esub> V a \<guillemotleft> on_suffix n \<E>)"
proof -
  have "\<Delta>\<^bsub>i\<^esub> (V \<guillemotleft> on_suffix (Suc n) \<E>) = \<Delta> (V \<guillemotleft> on_suffix (Suc n) \<E> \<guillemotleft> move 0 i)"
    by transfer simp
  also have "\<dots> = \<Delta> (V \<guillemotleft> move 0 i \<guillemotleft> on_suffix (Suc n) \<E>)"
    using \<open>i \<le> n\<close>
    by (simp only: composition_adapted [symmetric] move_after_on_suffix)
  also have "\<dots> = (\<lambda>a. \<Delta> (V \<guillemotleft> move 0 i) a \<guillemotleft> on_suffix n \<E>)"
    using family_curry_after_on_suffix_adapted .
  also have "\<dots> = (\<lambda>a. \<Delta>\<^bsub>i\<^esub> V a \<guillemotleft> on_suffix n \<E>)"
    by transfer simp
  finally show ?thesis .
qed

lemma on_suffix_adapted_after_deep_uncurry:
  assumes "i \<le> n"
  shows "\<nabla>\<^bsub>i\<^esub> \<V> \<guillemotleft> on_suffix (Suc n) \<E> = \<nabla>\<^bsub>i\<^esub> (\<lambda>a. \<V> a \<guillemotleft> on_suffix n \<E>)"
proof -
  have "\<nabla>\<^bsub>i\<^esub> \<V> \<guillemotleft> on_suffix (Suc n) \<E> = \<nabla> \<V> \<guillemotleft> move i 0 \<guillemotleft> on_suffix (Suc n) \<E>"
    by transfer (simp add: comp_def)
  also have "\<dots> = \<nabla> \<V> \<guillemotleft> on_suffix (Suc n) \<E> \<guillemotleft> move i 0"
    using \<open>i \<le> n\<close>
    by (simp only: composition_adapted [symmetric] move_after_on_suffix)
  also have "\<dots> = \<nabla> (\<lambda>a. \<V> a \<guillemotleft> on_suffix n \<E>) \<guillemotleft> move i 0"
    by (simp only: on_suffix_adapted_after_family_uncurry)
  also have "\<dots> = \<nabla>\<^bsub>i\<^esub> (\<lambda>a. \<V> a \<guillemotleft> on_suffix n \<E>)"
    by transfer (simp add: comp_def)
  finally show ?thesis .
qed

lemma family_uncurry_and_on_suffix_adapted:
  assumes "\<nabla> \<V>' = W \<guillemotleft> on_suffix (Suc n) \<E>"
  obtains \<V> where "\<V>' = (\<lambda>a. \<V> a \<guillemotleft> on_suffix n \<E>)" and "W = \<nabla> \<V>"
proof -
  have "\<V>' = (\<lambda>a. \<Delta> W a \<guillemotleft> on_suffix n \<E>)"
  proof -
    have "\<V>' = \<Delta> (\<nabla> \<V>')"
      by simp
    also have "\<dots> = \<Delta> (W \<guillemotleft> on_suffix (Suc n) \<E>)"
      using \<open>\<nabla> \<V>' = W \<guillemotleft> on_suffix (Suc n) \<E>\<close>
      by simp
    also have "\<dots> = (\<lambda>a. \<Delta> W a \<guillemotleft> on_suffix n \<E>)"
      by (simp only: family_curry_after_on_suffix_adapted)
    finally show ?thesis .
  qed
  moreover have "W = \<nabla> (\<Delta> W)"
    by simp
  ultimately show ?thesis
    using that
    by blast
qed

lemma deep_uncurry_and_on_suffix_adapted:
  assumes "i \<le> n" and "\<nabla>\<^bsub>i\<^esub> \<V>' = W \<guillemotleft> on_suffix (Suc n) \<E>"
  obtains \<V> where "\<V>' = (\<lambda>a. \<V> a \<guillemotleft> on_suffix n \<E>)" and "W = \<nabla>\<^bsub>i\<^esub> \<V>"
proof -
  from assms(2) have "\<nabla> \<V>' \<guillemotleft> move i 0 = W \<guillemotleft> on_suffix (Suc n) \<E>"
    by transfer (simp add: comp_def)
  then obtain V where "\<nabla> \<V>' = V \<guillemotleft> on_suffix (Suc n) \<E>" and "W = V \<guillemotleft> move i 0"
    using move_adapted_and_on_suffix_adapted [OF le_imp_less_Suc [OF \<open>i \<le> n\<close>]]
    by blast
  from this(1) obtain \<V> where "\<V>' = (\<lambda>a. \<V> a \<guillemotleft> on_suffix n \<E>)" and "V = \<nabla> \<V>"
    using family_uncurry_and_on_suffix_adapted
    by blast
  from \<open>W = V \<guillemotleft> move i 0\<close> and \<open>V = \<nabla> \<V>\<close> have "W = \<nabla>\<^bsub>i\<^esub> \<V>"
    by transfer (simp add: comp_def)
  with that and \<open>\<V>' = (\<lambda>a. \<V> a \<guillemotleft> on_suffix n \<E>)\<close> show ?thesis .
qed

lemma constant_function_family_uncurry:
  shows "\<nabla> (\<lambda>_. A) = A \<guillemotleft> tail"
  unfolding tail_def
  by transfer (simp add: comp_def)

lemma constant_function_family_uncurry_as_remove_adapted:
  shows "\<nabla> (\<lambda>_. V) = V \<guillemotleft> remove 0"
  by transfer (simp add: comp_def)

lemma constant_function_deep_uncurry_as_remove_adapted:
  shows "\<nabla>\<^bsub>i\<^esub> (\<lambda>_. V) = V \<guillemotleft> remove i"
  by transfer (simp add: comp_def)

lemma family_curry_after_remove_adapted:
  shows "\<Delta> (V \<guillemotleft> remove (Suc i)) = (\<lambda>a. \<Delta> V a \<guillemotleft> remove i)"
  by transfer (simp add: comp_def)

lemma remove_adapted_after_family_uncurry:
  shows "\<nabla> \<V> \<guillemotleft> remove (Suc i) = \<nabla> (\<lambda>a. \<V> a \<guillemotleft> remove i)"
  by transfer (simp add: comp_def)

(* NOTE:
  With \<^theory_text>\<open>deep\<close> instead of \<^theory_text>\<open>deeper\<close>, the following lemmas would have to have the inequalities kind
  of reversed, making them analogous to the \<^theory_text>\<open>family\<close> versions.
*)

lemma deeper_curry_after_remove_adapted:
  assumes "i \<le> n"
  shows "\<Delta>\<^bsub>Suc n\<^esub> (V \<guillemotleft> remove i) = (\<lambda>a. \<Delta>\<^bsub>n\<^esub> V a \<guillemotleft> remove i)"
  using assms
  by
    transfer
    (
      simp
        del: stake.simps(2) sdrop.simps(2)
        add: comp_def stake_shift sdrop_shift,
      simp
        del: stake.simps(2)
        add: take_stake min_absorb1 drop_stake
    )

lemma remove_adapted_after_deeper_uncurry:
  assumes "i \<le> n"
  shows "\<nabla>\<^bsub>n\<^esub> \<V> \<guillemotleft> remove i = \<nabla>\<^bsub>Suc n\<^esub> (\<lambda>a. \<V> a \<guillemotleft> remove i)"
  using assms
  by
    transfer
    (
      simp
        del: stake.simps(2) sdrop.simps(2)
        add: comp_def stake_shift sdrop_shift sdrop_snth,
      simp
        del: stake.simps(2)
        add: take_stake min_absorb1 drop_stake
    )

lemma family_curry_after_move_adapted:
  shows "\<Delta> (V \<guillemotleft> move (Suc i) (Suc j)) = (\<lambda>a. \<Delta> V a \<guillemotleft> move i j)"
  by transfer (simp add: comp_def)

lemma move_adapted_after_family_uncurry:
  shows "\<nabla> \<V> \<guillemotleft> move (Suc i) (Suc j) = \<nabla> (\<lambda>a. \<V> a \<guillemotleft> move i j)"
  by transfer (simp add: comp_def)

(* NOTE:
  With \<^theory_text>\<open>deep\<close> instead of \<^theory_text>\<open>deeper\<close>, the following lemmas would have to have the inequalities kind
  of reversed, making them analogous to the \<^theory_text>\<open>family\<close> versions.
*)

lemma deeper_curry_after_move_adapted:
  assumes "i < n" and "j < n"
  shows "\<Delta>\<^bsub>n\<^esub> (V \<guillemotleft> move i j) = (\<lambda>a. \<Delta>\<^bsub>n\<^esub> V a \<guillemotleft> move i j)"
proof -
  have "\<Delta>\<^bsub>n\<^esub> (V \<guillemotleft> move i j) = \<Delta> (V \<guillemotleft> move i j \<guillemotleft> move 0 n)"
    by transfer simp
  also have "\<dots> = \<Delta> (V \<guillemotleft> move 0 n \<guillemotleft> move (Suc i) (Suc j))"
    using \<open>i < n\<close> and \<open>j < n\<close>
    by (simp only: composition_adapted [symmetric] move_after_outer_move_away_from_front)
  also have "\<dots> = (\<lambda>a. \<Delta> (V \<guillemotleft> move 0 n) a \<guillemotleft> move i j)"
    by (simp only: family_curry_after_move_adapted)
  also have "\<dots> = (\<lambda>a. \<Delta>\<^bsub>n\<^esub> V a \<guillemotleft> move i j)"
    by transfer simp
  finally show ?thesis .
qed

lemma move_adapted_after_deeper_uncurry:
  assumes "i < n" and "j < n"
  shows "\<nabla>\<^bsub>n\<^esub> \<V> \<guillemotleft> move i j = \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<V> a \<guillemotleft> move i j)"
proof -
  have "\<nabla>\<^bsub>n\<^esub> \<V> \<guillemotleft> move i j = \<nabla> \<V> \<guillemotleft> move n 0 \<guillemotleft> move i j"
    by transfer (simp add: comp_def)
  also have "\<dots> = \<nabla> \<V> \<guillemotleft> move (Suc i) (Suc j) \<guillemotleft> move n 0"
    using \<open>i < n\<close> and \<open>j < n\<close>
    by (simp only: composition_adapted [symmetric] outer_move_towards_front_after_move)
  also have "\<dots> = \<nabla> (\<lambda>a. \<V> a \<guillemotleft> move i j) \<guillemotleft> move n 0"
    by (simp only: move_adapted_after_family_uncurry)
  also have "\<dots> = \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<V> a \<guillemotleft> move i j)"
    by transfer (simp add: comp_def)
  finally show ?thesis .
qed

lemma source_curry_after_move_adapted:
  shows "\<Delta>\<^bsub>i\<^esub> (V \<guillemotleft> move i j) = \<Delta>\<^bsub>j\<^esub> V"
  using delete_at_after_insert_at
  by transfer auto

lemma move_adapted_after_source_uncurry:
  shows "\<nabla>\<^bsub>j\<^esub> \<V> \<guillemotleft> move i j = \<nabla>\<^bsub>i\<^esub> \<V>"
  using delete_at_after_insert_at
  by transfer auto

lemma deep_uncurry_reordering:
  assumes "i \<ge> j"
  shows "\<nabla>\<^bsub>Suc i\<^esub> (\<lambda>a. \<nabla>\<^bsub>j\<^esub> (\<lambda>b. \<V> a b)) = \<nabla>\<^bsub>j\<^esub> (\<lambda>b. \<nabla>\<^bsub>i\<^esub> (\<lambda>a. \<V> a b))"
  using assms
  by
    (simp
      del: stake.simps(2) sdrop.simps(2)
      add: sdrop_snth stake_shift sdrop_shift take_stake min_absorb1 min_absorb2 drop_stake
    )

subsection \<open>Channel Families\<close>

lemma constant_family_chan_family_uncurry:
  shows "\<nabla> \<box> = shd"
  by simp

lemma chan_family_distinctness:
  fixes A :: "chan family"
  shows "shd \<noteq> A \<guillemotleft> tail" and "A \<guillemotleft> tail \<noteq> shd"
proof -
  obtain a :: chan and b :: chan where "a \<noteq> b"
    using more_than_one_chan
    by blast
  then show "shd \<noteq> A \<guillemotleft> tail"
  proof (cases "A undefined = a")
    case True
    with \<open>a \<noteq> b\<close> have "shd (b ## undefined) \<noteq> (A \<guillemotleft> tail) (b ## undefined)"
      unfolding tail_def
      by transfer simp
    then show ?thesis
      by auto
  next
    case False
    then have "shd (a ## undefined) \<noteq> (A \<guillemotleft> tail) (a ## undefined)"
      unfolding tail_def
      by transfer simp
    then show ?thesis
      by auto
  qed
  then show "A \<guillemotleft> tail \<noteq> shd"
    by simp
qed

end
