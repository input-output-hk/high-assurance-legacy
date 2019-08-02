theory Core_Bisimilarities
  imports Proper_Weak_Transition_System
begin

text \<open>
  We introduce a named theorem \<^theory_text>\<open>natural_simps\<close> that is analogous to \<^theory_text>\<open>algebra_simps\<close> in that it
  contains core laws like associativity and commutativity that are often, but not always, desired
  as rewrite rules.
\<close>

named_theorems natural_simps

context begin

private inductive
  parallel_scope_extension_left_subaux :: "process \<Rightarrow> process \<Rightarrow> process \<Rightarrow> bool"
  for q
where
  without_new_channel: "
    parallel_scope_extension_left_subaux q p (p \<parallel> q)" |
  with_new_channel: "
    (\<And>a. parallel_scope_extension_left_subaux q (P a) (R a)) \<Longrightarrow>
    parallel_scope_extension_left_subaux q (\<nu> a. P a) (\<nu> a. R a)"

private method parallel_scope_extension_left_subaux_trivial_conveyance uses intro =
  (blast intro: intro parallel_scope_extension_left_subaux.without_new_channel)

private method parallel_scope_extension_left_subaux_communication_conveyance =
  (parallel_scope_extension_left_subaux_trivial_conveyance intro: communication)

private method parallel_scope_extension_left_subaux_acting_left_conveyance =
  (parallel_scope_extension_left_subaux_trivial_conveyance intro: acting_left)

private method parallel_scope_extension_left_subaux_opening_left_conveyance =
  (parallel_scope_extension_left_subaux_trivial_conveyance intro: opening_left)

private lemma parallel_scope_extension_left_subaux_opening_conveyance:
  assumes initial_relation: "parallel_scope_extension_left_subaux q p t"
  assumes transition: "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a"
  shows "\<exists>T. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T a \<and> (\<forall>a. parallel_scope_extension_left_subaux q (P a) (T a))"
using transition and initial_relation and transition
proof (induction (no_simp) p "\<lbrace>\<nu> a\<rbrace> P a" arbitrary: P t)
  case (opening P P' t)
  from opening.prems show ?case
  proof cases
    case with_new_channel
    with \<open>\<lbrace>\<nu> a\<rbrace> P a = \<lbrace>\<nu> a\<rbrace> P' a\<close> show ?thesis
      using basic_transition.opening
      by blast
  qed parallel_scope_extension_left_subaux_opening_left_conveyance
next
  case opening_left
  from opening_left.prems show ?case
    by cases parallel_scope_extension_left_subaux_opening_left_conveyance
next
  case opening_right
  from opening_right.prems show ?case
    by cases parallel_scope_extension_left_subaux_opening_left_conveyance
next
  case (scoped_opening p P\<^sub>1 P\<^sub>2 P' t)
  from
    scoped_opening.IH(1) and
    \<open>parallel_scope_extension_left_subaux q p t\<close> and
    \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P\<^sub>1 a\<close>
  obtain T\<^sub>1 where
    "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
    "\<And>a. parallel_scope_extension_left_subaux q (P\<^sub>1 a) (T\<^sub>1 a)"
    by blast
  obtain T\<^sub>2 where
    "\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b" and
    "\<And>a b. parallel_scope_extension_left_subaux q (P\<^sub>2 a b) (T\<^sub>2 a b)"
  proof -
    from
      scoped_opening.IH(2) and
      \<open>\<And>a. parallel_scope_extension_left_subaux q (P\<^sub>1 a) (T\<^sub>1 a)\<close> and
      \<open>\<And>a. P\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P\<^sub>2 a b\<close>
    have "
      \<forall>a. \<exists>V. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> V b \<and> (\<forall>b. parallel_scope_extension_left_subaux q (P\<^sub>2 a b) (V b))"
      by blast
    then have "
      \<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b \<and> (\<forall>b. parallel_scope_extension_left_subaux q (P\<^sub>2 a b) (T\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a\<close> and \<open>\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b\<close> have "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. T\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with
    \<open>\<lbrace>\<nu> b\<rbrace> \<nu> a. P\<^sub>2 a b = \<lbrace>\<nu> b\<rbrace> P' b\<close> and
    \<open>\<And>a b. parallel_scope_extension_left_subaux q (P\<^sub>2 a b) (T\<^sub>2 a b)\<close>
  show ?case
    using basic_residual.inject(2) and parallel_scope_extension_left_subaux.with_new_channel
    by smt
qed simp_all

private inductive
  parallel_scope_extension_left_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel_ltr: "
    parallel_scope_extension_left_subaux q p r \<Longrightarrow> parallel_scope_extension_left_aux (p \<parallel> q) r" |
  without_new_channel_rtl: "
    parallel_scope_extension_left_subaux q p r \<Longrightarrow> parallel_scope_extension_left_aux r (p \<parallel> q)" |
  with_new_channel: "
    (\<And>a. parallel_scope_extension_left_aux (S a) (T a)) \<Longrightarrow>
    parallel_scope_extension_left_aux (\<nu> a. S a) (\<nu> a. T a)"

private lemma parallel_scope_extension_left_aux_without_new_channel_normalization:
  assumes "parallel_scope_extension_left_aux (p \<parallel> q) t"
  shows "parallel_scope_extension_left_subaux q p t"
using assms proof cases
  case without_new_channel_ltr
  then show ?thesis by simp
next
  case without_new_channel_rtl
  then show ?thesis
    using
      parallel_scope_extension_left_subaux.cases and
      parallel_scope_extension_left_subaux.without_new_channel
    by blast
qed

lemma parallel_scope_extension_left: "\<nu> a. P a \<parallel> q \<sim>\<^sub>\<flat> \<nu> a. (P a \<parallel> q)"
proof (old_bisimilarity_standard parallel_scope_extension_left_aux)
  case related
  show ?case
    by (simp add:
      parallel_scope_extension_left_subaux.intros
      parallel_scope_extension_left_aux.without_new_channel_ltr)
next
  case sym
  then show ?case by induction (simp_all add: parallel_scope_extension_left_aux.intros)
next
  case (sim s t c)
  then show ?case
  proof (basic_sim_induction t with_new_channel: parallel_scope_extension_left_aux.with_new_channel)
    case (communication \<eta> \<mu> p p' q q' t)
    from communication.prems have "parallel_scope_extension_left_subaux q p t"
      by (fact parallel_scope_extension_left_aux_without_new_channel_normalization)
    from \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'\<close> and this and communication.hyps
    have "\<exists>t'. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> t' \<and> parallel_scope_extension_left_subaux q' p' t'"
    proof (induction (no_simp) p "\<lbrace>IO \<eta>\<rbrace> p'" arbitrary: p' t)
      case sending
      from sending.prems show ?case
        by cases parallel_scope_extension_left_subaux_communication_conveyance
    next
      case receiving
      from receiving.prems show ?case
        by cases parallel_scope_extension_left_subaux_communication_conveyance
    next
      case acting_left
      from acting_left.prems show ?case
        by cases parallel_scope_extension_left_subaux_communication_conveyance
    next
      case acting_right
      from acting_right.prems show ?case
        by cases parallel_scope_extension_left_subaux_communication_conveyance
    next
      case (scoped_acting p P\<^sub>1 \<beta> P\<^sub>2 p' t)
      from \<open>\<lbrace>\<beta>\<rbrace> \<nu> a. P\<^sub>2 a = \<lbrace>IO \<eta>\<rbrace> p'\<close> have "\<beta> = IO \<eta>" and "p' = \<nu> a. P\<^sub>2 a"
        by simp_all
      from \<open>parallel_scope_extension_left_subaux q p t\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P\<^sub>1 a\<close>
      obtain T\<^sub>1 where
        "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
        "\<And>a. parallel_scope_extension_left_subaux q (P\<^sub>1 a) (T\<^sub>1 a)"
        using parallel_scope_extension_left_subaux_opening_conveyance
        by blast
      obtain T\<^sub>2 where
        "\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a" and
        "\<And>a. parallel_scope_extension_left_subaux q' (P\<^sub>2 a) (T\<^sub>2 a)"
      proof -
        from
          \<open>\<beta> = IO \<eta>\<close> and
          scoped_acting.IH(2) and
          \<open>\<And>a. parallel_scope_extension_left_subaux q (P\<^sub>1 a) (T\<^sub>1 a)\<close> and
          \<open>\<eta> \<bowtie> \<mu>\<close> and
          \<open>\<And>a. P\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<beta>\<rbrace> P\<^sub>2 a\<close> and
          \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q'\<close>
        have "\<forall>a. \<exists>v. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> v \<and> parallel_scope_extension_left_subaux q' (P\<^sub>2 a) v"
          by blast
        then have
          "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a \<and> parallel_scope_extension_left_subaux q' (P\<^sub>2 a) (T\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a\<close> and \<open>\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a\<close> have "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. T\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with \<open>p' = \<nu> a. P\<^sub>2 a\<close> and \<open>\<And>a. parallel_scope_extension_left_subaux q' (P\<^sub>2 a) (T\<^sub>2 a)\<close>
      show ?case
        using parallel_scope_extension_left_subaux.with_new_channel
        by blast
    qed simp_all
    then show ?case
      using parallel_scope_extension_left_aux.without_new_channel_ltr and acting_lift
      by auto
  next
    case (opening S t)
    from opening.prems show ?case
    proof cases
      case (without_new_channel_rtl q p)
      from \<open>parallel_scope_extension_left_subaux q p (\<nu> a. S a)\<close> show ?thesis
      proof cases
        case with_new_channel
        with \<open>t = p \<parallel> q\<close> show ?thesis
          using
            basic_transition.opening and
            opening_left and
            parallel_scope_extension_left_aux.without_new_channel_rtl and
            opening_lift and
            rel_funI
          by (metis (mono_tags, lifting))
      qed
    next
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift and rel_funI
        by metis
    qed
  next
    case (acting_left p \<alpha> p' q t)
    from acting_left.prems have "parallel_scope_extension_left_subaux q p t"
      by (fact parallel_scope_extension_left_aux_without_new_channel_normalization)
    from \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p'\<close> and this and acting_left.hyps
    have "\<exists>t'. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t' \<and> parallel_scope_extension_left_subaux q p' t'"
    proof (induction (no_simp) p "\<lbrace>\<alpha>\<rbrace> p'" arbitrary: p' t)
      case sending
      from sending.prems show ?case
        by cases parallel_scope_extension_left_subaux_acting_left_conveyance
    next
      case receiving
      from receiving.prems show ?case
        by cases parallel_scope_extension_left_subaux_acting_left_conveyance
    next
      case communication
      from communication.prems show ?case
        by cases parallel_scope_extension_left_subaux_acting_left_conveyance
    next
      case acting_left
      from acting_left.prems show ?case
        by cases parallel_scope_extension_left_subaux_acting_left_conveyance
    next
      case acting_right
      from acting_right.prems show ?case
        by cases parallel_scope_extension_left_subaux_acting_left_conveyance
    next
      case (scoped_acting p P\<^sub>1 \<beta> P\<^sub>2 p' t)
      from \<open>\<lbrace>\<beta>\<rbrace> \<nu> a. P\<^sub>2 a = \<lbrace>\<alpha>\<rbrace> p'\<close> have "\<beta> = \<alpha>" and "p' = \<nu> a. P\<^sub>2 a"
        by simp_all
      from \<open>parallel_scope_extension_left_subaux q p t\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P\<^sub>1 a\<close>
      obtain T\<^sub>1 where
        "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
        "\<And>a. parallel_scope_extension_left_subaux q (P\<^sub>1 a) (T\<^sub>1 a)"
        using parallel_scope_extension_left_subaux_opening_conveyance
        by blast
      obtain T\<^sub>2 where
        "\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a" and
        "\<And>a. parallel_scope_extension_left_subaux q (P\<^sub>2 a) (T\<^sub>2 a)"
      proof -
        from
          \<open>\<beta> = \<alpha>\<close> and
          scoped_acting.IH(2) and
          \<open>\<And>a. parallel_scope_extension_left_subaux q (P\<^sub>1 a) (T\<^sub>1 a)\<close> and
          \<open>\<And>a. P\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<beta>\<rbrace> P\<^sub>2 a\<close>
        have "\<forall>a. \<exists>v. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> v \<and> parallel_scope_extension_left_subaux q (P\<^sub>2 a) v"
          by blast
        then have
          "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a \<and> parallel_scope_extension_left_subaux q (P\<^sub>2 a) (T\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a\<close> and \<open>\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a\<close> have "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. T\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with \<open>p' = \<nu> a. P\<^sub>2 a\<close> and \<open>\<And>a. parallel_scope_extension_left_subaux q (P\<^sub>2 a) (T\<^sub>2 a)\<close>
      show ?case
        using parallel_scope_extension_left_subaux.with_new_channel
        by blast
    qed simp_all
    then show ?case
      using parallel_scope_extension_left_aux.without_new_channel_ltr and acting_lift
      by auto
  next
    case (acting_right q \<alpha> q' p t)
    from acting_right.prems have "parallel_scope_extension_left_subaux q p t"
      by (fact parallel_scope_extension_left_aux_without_new_channel_normalization)
    from this and acting_right.hyps
    have "\<exists>t'. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t' \<and> parallel_scope_extension_left_subaux q' p t'"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.acting_right and
          parallel_scope_extension_left_subaux.without_new_channel
        by blast
    next
      case (with_new_channel P T)
      then have "
        \<forall>a. \<exists>v. T a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> v \<and> parallel_scope_extension_left_subaux q' (P a) v"
        by simp
      then have "
        \<exists>T'. \<forall>a. T a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' a \<and> parallel_scope_extension_left_subaux q' (P a) (T' a)"
        by (fact choice)
      then show ?case
        using acting_scope and parallel_scope_extension_left_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using parallel_scope_extension_left_aux.without_new_channel_ltr and opening_lift
      by auto
  next
    case (opening_left p P q t)
    from opening_left.prems have "parallel_scope_extension_left_subaux q p t"
      by (fact parallel_scope_extension_left_aux_without_new_channel_normalization)
    with opening_left.hyps show ?case
      using
        parallel_scope_extension_left_subaux_opening_conveyance and
        parallel_scope_extension_left_aux.without_new_channel_ltr and
        opening_lift and
        rel_funI
      by smt
  next
    case (opening_right q Q p t)
    from opening_right.prems have "parallel_scope_extension_left_subaux q p t"
      by (fact parallel_scope_extension_left_aux_without_new_channel_normalization)
    from this and opening_right.hyps
    have "\<exists>T. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T a \<and> (\<forall>a. parallel_scope_extension_left_subaux (Q a) p (T a))"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.opening_right and
          parallel_scope_extension_left_subaux.without_new_channel
        by blast
    next
      case (with_new_channel P T)
      then have "
        \<forall>a. \<exists>V. T a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> V b \<and> (\<forall>b. parallel_scope_extension_left_subaux (Q b) (P a) (V b))"
        by simp
      then have "
        \<exists>T'. \<forall>a. T a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T' a b \<and> (\<forall>b. parallel_scope_extension_left_subaux (Q b) (P a) (T' a b))"
        by (fact choice)
      then show ?case
        using opening_scope and parallel_scope_extension_left_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using
        parallel_scope_extension_left_aux.without_new_channel_ltr and
        opening_lift and
        rel_funI
      by smt
  qed (blast elim:
    parallel_scope_extension_left_subaux.cases
    parallel_scope_extension_left_aux.cases)+
qed

end

lemma parallel_scope_extension_right: "p \<parallel> \<nu> a. Q a \<sim>\<^sub>\<flat> \<nu> a. (p \<parallel> Q a)"
  sorry

context begin

private lemma pre_new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<lesssim>\<^sub>\<flat> \<nu> a. \<nu> b. P a b"
proof (standard, intro allI, intro impI)
  fix c
  assume "\<nu> b. \<nu> a. P a b \<rightarrow>\<^sub>\<flat>c"
  then have "\<nu> a. \<nu> b. P a b \<rightarrow>\<^sub>\<flat>c"
  proof (induction "\<nu> b. \<nu> a. P a b" c)
    case opening
    show ?case using basic_transition.opening by (intro opening_scope)
  next
    case scoped_acting
    then show ?case by (simp add: basic_transition.scoped_acting)
  next
    case scoped_opening
    then show ?case by (simp add: basic_transition.scoped_opening)
  qed
  show "\<exists>d. \<nu> a. \<nu> b. P a b \<rightarrow>\<^sub>\<flat>d \<and> basic_lift (\<lambda>p q. p \<lesssim>\<^sub>\<flat> q \<and> q \<lesssim>\<^sub>\<flat> p) c d"
  proof -
    have "basic_lift (\<lambda>p q. p \<lesssim>\<^sub>\<flat> q \<and> q \<lesssim>\<^sub>\<flat> p) c c"
      using
        basic_residual.rel_refl and
        basic.bisimilarity_def and
        basic.bisimilarity_reflexivity_rule
      by (metis (no_types, lifting))
    with \<open>\<nu> a. \<nu> b. P a b \<rightarrow>\<^sub>\<flat>c\<close> show ?thesis by blast
  qed
qed

lemma new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<sim>\<^sub>\<flat> \<nu> a. \<nu> b. P a b"
  by (simp add: pre_new_channel_scope_extension basic.bisimilarity_def)

end

context begin

private inductive
  parallel_neutrality_left_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel_ltr: "
    parallel_neutrality_left_aux (\<zero> \<parallel> p) p" |
  without_new_channel_rtl: "
    parallel_neutrality_left_aux p (\<zero> \<parallel> p)" |
  with_new_channel: "
    (\<And>a. parallel_neutrality_left_aux (S a) (T a)) \<Longrightarrow>
    parallel_neutrality_left_aux (\<nu> a. S a) (\<nu> a. T a)"

private method parallel_neutrality_left_aux_trivial_conveyance =
  (blast intro:
    acting_right
    opening_right
    parallel_neutrality_left_aux.without_new_channel_rtl
    basic_lift_intros
  )

lemma basic_parallel_neutrality_left [natural_simps]: "\<zero> \<parallel> p \<sim>\<^sub>\<flat> p"
proof (old_bisimilarity_standard parallel_neutrality_left_aux)
  case related
  show ?case by (fact parallel_neutrality_left_aux.without_new_channel_ltr)
next
  case sym
  then show ?case by induction (simp_all add: parallel_neutrality_left_aux.intros)
next
  case (sim s t c)
  from this and \<open>s \<rightarrow>\<^sub>\<flat>c\<close> show ?case
  proof (basic_sim_induction t with_new_channel: parallel_neutrality_left_aux.with_new_channel)
    case sending
    from sending.prems show ?case
      by cases parallel_neutrality_left_aux_trivial_conveyance
  next
    case receiving
    from receiving.prems show ?case
      by cases parallel_neutrality_left_aux_trivial_conveyance
  next
    case communication
    from communication.prems show ?case
    proof cases
      case without_new_channel_ltr
      with communication.hyps show ?thesis
        by (simp add: no_basic_transitions_from_stop)
    qed parallel_neutrality_left_aux_trivial_conveyance
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift and rel_funI
        by metis
    qed parallel_neutrality_left_aux_trivial_conveyance
  next
    case acting_left
    from acting_left.prems show ?case
    proof cases
      case without_new_channel_ltr
      with acting_left.hyps show ?thesis
        by (simp add: no_basic_transitions_from_stop)
    qed parallel_neutrality_left_aux_trivial_conveyance
  next
    case acting_right
    from acting_right.prems show ?case
    proof cases
      case without_new_channel_ltr
      with acting_right.hyps show ?thesis
        using parallel_neutrality_left_aux.without_new_channel_ltr and acting_lift
        by auto
    qed parallel_neutrality_left_aux_trivial_conveyance
  next
    case opening_left
    from opening_left.prems show ?case
    proof cases
      case without_new_channel_ltr
      with opening_left.hyps show ?thesis
        by (simp add: no_basic_transitions_from_stop)
    qed parallel_neutrality_left_aux_trivial_conveyance
  next
    case opening_right
    from opening_right.prems show ?case
    proof cases
      case without_new_channel_ltr
      with opening_right.hyps show ?thesis
        using
          parallel_neutrality_left_aux.without_new_channel_ltr and
          opening_lift and
          rel_funI
        by smt
    qed parallel_neutrality_left_aux_trivial_conveyance
  qed
qed

lemma parallel_neutrality_right [natural_simps]: "p \<parallel> \<zero> \<sim>\<^sub>\<flat> p"
  sorry

end

context begin

private inductive
  nested_parallel_commutativity_subaux :: "process \<Rightarrow> process \<Rightarrow> process \<Rightarrow> bool"
  for r
where
  without_new_channel: "
    nested_parallel_commutativity_subaux r (p \<parallel> q) ((p \<parallel> r) \<parallel> q)" |
  with_new_channel: "
    (\<And>a. nested_parallel_commutativity_subaux r (U a) (T a)) \<Longrightarrow>
    nested_parallel_commutativity_subaux r (\<nu> a. U a) (\<nu> a. T a)"

private lemma nested_parallel_commutativity_subaux_opening_conveyance:
  assumes initial_relation: "nested_parallel_commutativity_subaux r u t"
  assumes transition: "u \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> U a"
  shows "\<exists>T. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T a \<and> (\<forall>a. nested_parallel_commutativity_subaux r (U a) (T a))"
using transition and initial_relation
proof (induction u "\<lbrace>\<nu> a\<rbrace> U a" arbitrary: U t)
  case (opening U t)
  from opening.prems show ?case
  proof cases
    case with_new_channel
    then show ?thesis
      using basic_transition.opening
      by blast
  qed
next
  case (opening_left p P q t)
  from opening_left.prems show ?case
  proof cases
    case without_new_channel
    with \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close> show ?thesis
      using
        basic_transition.opening_left and
        nested_parallel_commutativity_subaux.without_new_channel
      by blast
  qed
next
  case (opening_right q Q p t)
  from opening_right.prems show ?case
  proof cases
    case without_new_channel
    with \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a\<close> show ?thesis
      using
        basic_transition.opening_right and
        nested_parallel_commutativity_subaux.without_new_channel
      by blast
  qed
next
  case (scoped_opening u U\<^sub>1 U\<^sub>2 t)
  from scoped_opening.hyps(2) and \<open>nested_parallel_commutativity_subaux r u t\<close>
  obtain T\<^sub>1 where
    "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
    "\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)"
    by blast
  obtain T\<^sub>2 where
    "\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b" and
    "\<And>a b. nested_parallel_commutativity_subaux r (U\<^sub>2 a b) (T\<^sub>2 a b)"
  proof -
    from scoped_opening.hyps(4) and \<open>\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)\<close>
    have "
      \<forall>a. \<exists>V. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> V b \<and> (\<forall>b. nested_parallel_commutativity_subaux r (U\<^sub>2 a b) (V b))"
      by blast
    then have "
      \<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b \<and> (\<forall>b. nested_parallel_commutativity_subaux r (U\<^sub>2 a b) (T\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a\<close> and \<open>\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b\<close> have "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. T\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with \<open>\<And>a b. nested_parallel_commutativity_subaux r (U\<^sub>2 a b) (T\<^sub>2 a b)\<close> show ?case
    using nested_parallel_commutativity_subaux.with_new_channel
    by metis
qed

private inductive
  nested_parallel_commutativity_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel_ltr: "
    nested_parallel_commutativity_subaux r u t \<Longrightarrow>
    nested_parallel_commutativity_aux (u \<parallel> r) t" |
  without_new_channel_rtl: "
    nested_parallel_commutativity_subaux r u s \<Longrightarrow>
    nested_parallel_commutativity_aux s (u \<parallel> r)" |
  with_new_channel: "
    (\<And>a. nested_parallel_commutativity_aux (S a) (T a)) \<Longrightarrow>
    nested_parallel_commutativity_aux (\<nu> a. S a) (\<nu> a. T a)"

private lemma nested_parallel_commutativity_aux_without_new_channel_normalization:
  assumes "nested_parallel_commutativity_aux (u \<parallel> r) t"
  shows "nested_parallel_commutativity_subaux r u t"
using assms proof cases
  case without_new_channel_ltr
  then show ?thesis by simp
next
  case without_new_channel_rtl
  then show ?thesis
    using
      nested_parallel_commutativity_subaux.cases and
      nested_parallel_commutativity_subaux.without_new_channel
    by blast
qed

private lemma basic_nested_parallel_commutativity: "(p \<parallel> q) \<parallel> r \<sim>\<^sub>\<flat> (p \<parallel> r) \<parallel> q"
proof (old_bisimilarity_standard nested_parallel_commutativity_aux)
  case related
  show ?case
    by (simp add:
      nested_parallel_commutativity_subaux.without_new_channel
      nested_parallel_commutativity_aux.without_new_channel_ltr)
next
  case sym
  then show ?case by induction (simp_all add: nested_parallel_commutativity_aux.intros)
next
  case (sim s t c)
  then show ?case
  proof (basic_sim_induction t with_new_channel: nested_parallel_commutativity_aux.with_new_channel)
    case (communication \<eta> \<mu> u u' r r' t)
    from communication.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with \<open>u \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> u'\<close>
    have "\<exists>t'. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> t' \<and> nested_parallel_commutativity_subaux r' u' t'"
    proof (induction u "\<lbrace>IO \<eta>\<rbrace> u'" arbitrary: u' t)
      case (acting_left p p' q t)
      from acting_left.prems show ?case
      proof cases
        case without_new_channel
        with \<open>\<eta> \<bowtie> \<mu>\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'\<close> and \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> r'\<close> show ?thesis
          using
            basic_transition.communication and
            basic_transition.acting_left and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_right q q' p t)
      from acting_right.prems show ?case
      proof cases
        case without_new_channel
        with \<open>\<eta> \<bowtie> \<mu>\<close> and \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> q'\<close> and \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> r'\<close> show ?thesis
          using
            communication_symmetry_rule and
            basic_transition.acting_right and
            basic_transition.communication and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (scoped_acting u U\<^sub>1 U\<^sub>2 t)
      from \<open>nested_parallel_commutativity_subaux r u t\<close> and \<open>u \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> U\<^sub>1 a\<close>
      obtain T\<^sub>1 where
        "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
        "\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)"
        using nested_parallel_commutativity_subaux_opening_conveyance
        by blast
      obtain T\<^sub>2 where
        "\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a" and
        "\<And>a. nested_parallel_commutativity_subaux r' (U\<^sub>2 a) (T\<^sub>2 a)"
      proof -
        from
          scoped_acting.hyps(3) and
          \<open>\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)\<close>
        have "\<forall>a. \<exists>v. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> v \<and> nested_parallel_commutativity_subaux r' (U\<^sub>2 a) v"
          by blast
        then have
          "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a \<and> nested_parallel_commutativity_subaux r' (U\<^sub>2 a) (T\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a\<close> and \<open>\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> T\<^sub>2 a\<close> have "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. T\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with \<open>\<And>a. nested_parallel_commutativity_subaux r' (U\<^sub>2 a) (T\<^sub>2 a)\<close>
      show ?case
        using nested_parallel_commutativity_subaux.with_new_channel
        by blast
    qed (blast elim: nested_parallel_commutativity_subaux.cases)+
    then show ?case
      using
        nested_parallel_commutativity_aux.without_new_channel_ltr and
        acting_lift
      by auto
  next
    case (opening S t)
    from opening.prems show ?case
    proof cases
      case (without_new_channel_rtl r u)
      from \<open>nested_parallel_commutativity_subaux r u (\<nu> a. S a)\<close> show ?thesis
      proof cases
        case with_new_channel
        with \<open>t = u \<parallel> r\<close> show ?thesis
          using
            basic_transition.opening and
            opening_left and
            nested_parallel_commutativity_aux.without_new_channel_rtl and
            opening_lift and
            rel_funI
          by (metis (mono_tags, lifting))
      qed
    next
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift
        by blast
    qed
  next
    case (acting_left u \<alpha> u' r t)
    from acting_left.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with \<open>u \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> u'\<close>
    have "\<exists>t'. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t' \<and> nested_parallel_commutativity_subaux r u' t'"
    proof (induction u "\<lbrace>\<alpha>\<rbrace> u'" arbitrary: u' t)
      case (communication \<eta> \<mu> p p' q q' t)
      from communication.prems show ?case
      proof cases
        case without_new_channel
        with \<open>\<tau> = \<alpha>\<close> and \<open>\<eta> \<bowtie> \<mu>\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'\<close> and \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q'\<close> show ?thesis
          using
            basic_transition.acting_left and
            basic_transition.communication and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_left p p' q t)
      from acting_left.prems show ?case
      proof cases
        case without_new_channel
        with \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p'\<close> show ?thesis
          using
            basic_transition.acting_left and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (acting_right q q' p t)
      from acting_right.prems show ?case
      proof cases
        case without_new_channel
        with \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'\<close> show ?thesis
          using
            basic_transition.acting_right and
            nested_parallel_commutativity_subaux.without_new_channel
          by blast
      qed
    next
      case (scoped_acting u U\<^sub>1 U\<^sub>2 t)
      from \<open>nested_parallel_commutativity_subaux r u t\<close> and \<open>u \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> U\<^sub>1 a\<close>
      obtain T\<^sub>1 where
        "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and
        "\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)"
        using nested_parallel_commutativity_subaux_opening_conveyance
        by blast
      obtain T\<^sub>2 where
        "\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a" and
        "\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>2 a) (T\<^sub>2 a)"
      proof -
        from
          scoped_acting.hyps(3) and
          \<open>\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>1 a) (T\<^sub>1 a)\<close>
        have "\<forall>a. \<exists>v. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> v \<and> nested_parallel_commutativity_subaux r (U\<^sub>2 a) v"
          by blast
        then have
          "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a \<and> nested_parallel_commutativity_subaux r (U\<^sub>2 a) (T\<^sub>2 a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      from \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a\<close> and \<open>\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a\<close> have "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. T\<^sub>2 a"
        by (fact basic_transition.scoped_acting)
      with \<open>\<And>a. nested_parallel_commutativity_subaux r (U\<^sub>2 a) (T\<^sub>2 a)\<close>
      show ?case
        using nested_parallel_commutativity_subaux.with_new_channel
        by blast
    qed (blast elim: nested_parallel_commutativity_subaux.cases)+
    then show ?case
      using
        nested_parallel_commutativity_aux.without_new_channel_ltr and
        acting_lift
      by auto
  next
    case (acting_right r \<alpha> r' u t)
    from acting_right.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    from this and acting_right.hyps
    have "\<exists>t'. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> t' \<and> nested_parallel_commutativity_subaux r' u t'"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.acting_right and
          basic_transition.acting_left and
          nested_parallel_commutativity_subaux.without_new_channel
        by blast
    next
      case (with_new_channel U T)
      then have "
        \<forall>a. \<exists>v. T a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> v \<and> nested_parallel_commutativity_subaux r' (U a) v"
        by simp
      then have "
        \<exists>T'. \<forall>a. T a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T' a \<and> nested_parallel_commutativity_subaux r' (U a) (T' a)"
        by (fact choice)
      then show ?case
        using acting_scope and nested_parallel_commutativity_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using
        nested_parallel_commutativity_aux.without_new_channel_ltr and
        acting_lift
      by auto
  next
    case (opening_left u U r t)
    from opening_left.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    with opening_left.hyps show ?case
      using
        nested_parallel_commutativity_subaux_opening_conveyance and
        nested_parallel_commutativity_aux.without_new_channel_ltr and
        opening_lift and
        rel_funI
      by smt
  next
    case (opening_right r R u t)
    from opening_right.prems have "nested_parallel_commutativity_subaux r u t"
      by (fact nested_parallel_commutativity_aux_without_new_channel_normalization)
    from this and opening_right.hyps
    have "\<exists>T. t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T a \<and> (\<forall>a. nested_parallel_commutativity_subaux (R a) u (T a))"
    proof induction
      case without_new_channel
      then show ?case
        using
          basic_transition.opening_right and
          basic_transition.opening_left and
          nested_parallel_commutativity_subaux.without_new_channel
        by blast
    next
      case (with_new_channel U T)
      then have "
        \<forall>a. \<exists>V. T a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> V b \<and> (\<forall>b. nested_parallel_commutativity_subaux (R b) (U a) (V b))"
        by simp
      then have "
        \<exists>T'. \<forall>a.
        T a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T' a b \<and> (\<forall>b. nested_parallel_commutativity_subaux (R b) (U a) (T' a b))"
        by (fact choice)
      then show ?case
        using opening_scope and nested_parallel_commutativity_subaux.with_new_channel
        by metis
    qed
    then show ?case
      using
        nested_parallel_commutativity_aux.without_new_channel_ltr and
        opening_lift and
        rel_funI
      by smt
  next
  qed (blast elim:
    nested_parallel_commutativity_subaux.cases
    nested_parallel_commutativity_aux.cases)+
qed

lemma parallel_commutativity [natural_simps]: "p \<parallel> q \<sim>\<^sub>\<flat> q \<parallel> p"
proof -
  have "p \<parallel> q \<sim>\<^sub>\<flat> (\<zero> \<parallel> p) \<parallel> q"
    using basic_parallel_neutrality_left and basic_parallel_preservation_left
    by (simp add: basic.bisimilarity_def)
  also have "(\<zero> \<parallel> p) \<parallel> q \<sim>\<^sub>\<flat> (\<zero> \<parallel> q) \<parallel> p"
    by (fact basic_nested_parallel_commutativity)
  also have "(\<zero> \<parallel> q) \<parallel> p \<sim>\<^sub>\<flat> q \<parallel> p"
    using basic_parallel_neutrality_left and basic_parallel_preservation_left by blast
  finally show ?thesis .
qed

lemma parallel_associativity [natural_simps]: "(p \<parallel> q) \<parallel> r \<sim>\<^sub>\<flat> p \<parallel> (q \<parallel> r)"
proof -
  have "(p \<parallel> q) \<parallel> r \<sim>\<^sub>\<flat> (q \<parallel> p) \<parallel> r"
    using parallel_commutativity and basic_parallel_preservation_left by blast
  also have "(q \<parallel> p) \<parallel> r \<sim>\<^sub>\<flat> (q \<parallel> r) \<parallel> p"
    by (fact basic_nested_parallel_commutativity)
  also have "(q \<parallel> r) \<parallel> p \<sim>\<^sub>\<flat> p \<parallel> (q \<parallel> r)"
    by (fact parallel_commutativity)
  finally show ?thesis .
qed

end

text \<open>
  Facts like the following are called left commutativity in Subsection~9.3.3 of the Isar Reference
  Manual. We do not use this term, as it would be inconsistent with our use of the words ``left''
  and ``right'' in other fact names.

  Currently there is a similar fact proved as a private lemma \<open>nested_parallel_commutativity\<close> above.
  Our goal for the future is to prove the lemma below directly and drop
  \<open>nested_parallel_commutativity\<close>.
\<close>

lemma parallel_nested_commutativity [natural_simps]: "p \<parallel> (q \<parallel> r) \<sim>\<^sub>\<flat> q \<parallel> (p \<parallel> r)"
  sorry

context begin

private lemma pre_receive_scope_extension_ltr: "a \<triangleright> x. \<nu> b. P x b \<lesssim>\<^sub>\<sharp> \<nu> b. a \<triangleright> x. P x b"
proof (standard, intro allI, intro impI)
  fix c
  assume "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>c"
  then show "\<exists>d. \<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>d \<and> proper_lift (\<lambda>p q. p \<lesssim>\<^sub>\<sharp> q \<and> q \<lesssim>\<^sub>\<sharp> p) c d"
  proof cases
    case (simple \<delta> q)
    from \<open>a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q\<close>
    obtain x where "basic_action_of \<delta> = a \<triangleright> x" and "q = \<nu> b. P x b"
      by (blast elim: basic_transitions_from_receive)
    from \<open>basic_action_of \<delta> = a \<triangleright> x\<close> have "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> b. P x b"
      using receiving and acting_scope
      by smt
    with \<open>c = \<lparr>\<delta>\<rparr> q\<close> and \<open>q = \<nu> b. P x b\<close> have "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>c"
      by (blast intro: proper_transition.simple)
    show ?thesis
    proof -
      have "proper_lift (\<lambda>p q. p \<lesssim>\<^sub>\<sharp> q \<and> q \<lesssim>\<^sub>\<sharp> p) c c"
        using local.simple(1) and proper.bisimilarity_def
        by auto
      with \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>c\<close> show ?thesis by blast
    qed
  next
    case (output_without_opening a x q)
    then show ?thesis
      by (blast elim: basic_transitions_from_receive)
  next
    case output_with_opening
    then show ?thesis
      using no_opening_transitions_from_receive
      by simp
  qed
qed

private lemma opening_transitions_from_new_channel_receive:
  "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b \<Longrightarrow> Q b = a \<triangleright> x . P x b"
proof (induction "\<nu> b. a \<triangleright> x. P x b" "\<lbrace>\<nu> b\<rbrace> Q b" arbitrary: Q rule: basic_transition.induct)
  case opening
  show ?case by (fact refl)
next
  case scoped_opening
  then show ?case using no_opening_transitions_from_receive by metis
qed

private lemma pre_receive_scope_extension_rtl: "\<nu> b. a \<triangleright> x. P x b \<lesssim>\<^sub>\<sharp> a \<triangleright> x. \<nu> b. P x b"
proof (standard, intro allI, intro impI)
  fix c
  assume "\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<sharp>c"
  then show "\<exists>d. a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>d \<and> proper_lift (\<lambda>p q. p \<lesssim>\<^sub>\<sharp> q \<and> q \<lesssim>\<^sub>\<sharp> p) c d"
  proof cases
    case (simple \<delta> r)
    from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> r\<close> show ?thesis
    proof cases
      case (scoped_acting Q R)
      from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b\<close> have "\<And>b. Q b = a \<triangleright> x . P x b"
        by (fact opening_transitions_from_new_channel_receive)
      with \<open>\<And>b. Q b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> R b\<close>
      obtain x where "basic_action_of \<delta> = a \<triangleright> x" and "\<And>b. R b = P x b"
        using
          basic_transitions_from_receive and
          basic_residual.inject(1) and
          basic_action.inject(1) and
          io_action.inject(2)
        by smt
      from \<open>basic_action_of \<delta> = a \<triangleright> x\<close> have "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> b. P x b"
        by (auto intro: receiving)
      moreover from \<open>c = \<lparr>\<delta>\<rparr> r\<close> and \<open>r = \<nu> b. R b\<close> and \<open>\<And>b. R b = P x b\<close> have "c = \<lparr>\<delta>\<rparr> \<nu> b. P x b"
        by simp
      ultimately have "a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>c"
        by (blast intro: proper_transition.simple)
      show ?thesis
      proof -
        have "proper_lift (\<lambda>p q. p \<lesssim>\<^sub>\<sharp> q \<and> q \<lesssim>\<^sub>\<sharp> p) c c"
          using
            proper_residual.rel_refl and
            proper.bisimilarity_def and
            proper.bisimilarity_reflexivity_rule
          by (metis (no_types, lifting))
        with \<open>a \<triangleright> x. \<nu> b. P x b \<rightarrow>\<^sub>\<sharp>c\<close> show ?thesis by blast
      qed
    qed
  next
    case (output_without_opening a' x r)
    from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>a' \<triangleleft> x\<rbrace> r\<close> show ?thesis
    proof cases
      case (scoped_acting Q R)
      from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b\<close> have "\<And>b. Q b = a \<triangleright> x. P x b"
        by (fact opening_transitions_from_new_channel_receive)
      with \<open>\<And>b. Q b \<rightarrow>\<^sub>\<flat>\<lbrace>a' \<triangleleft> x\<rbrace> R b\<close> show ?thesis
        by (auto elim: basic_transitions_from_receive)
    qed
  next
    case (output_with_opening Q a' K)
    from \<open>\<nu> b. a \<triangleright> x. P x b \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b\<close> have "\<And>b. Q b = a \<triangleright> x. P x b"
      by (fact opening_transitions_from_new_channel_receive)
    with \<open>\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a' \<triangleleft> K b\<close> have "a \<triangleright> x. P x undefined \<rightarrow>\<^sub>\<sharp>\<lparr>a' \<triangleleft> K undefined"
      by simp
    then show ?thesis
    proof cases
      case (output_without_opening x q)
      then show ?thesis
        by (blast elim: basic_transitions_from_receive)
    next
      case output_with_opening
      then show ?thesis
        using no_opening_transitions_from_receive
        by simp
    qed
  qed
qed

lemma receive_scope_extension [natural_simps]: "a \<triangleright> x. \<nu> b. P x b \<sim>\<^sub>\<sharp> \<nu> b. a \<triangleright> x. P x b"
  unfolding proper.bisimilarity_def
  by standard (
    fact pre_receive_scope_extension_ltr,
    fact pre_receive_scope_extension_rtl
  )

end

context begin

private lemma opening_transitions_from_new_channel_stop: "\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<Longrightarrow> P a = \<zero>"
proof -
  fix P and a
  assume "\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a"
  then show "P a = \<zero>"
  proof (induction "\<nu> a. \<zero>" "\<lbrace>\<nu> a\<rbrace> P a" arbitrary: P)
    case opening
    show ?case by (fact refl)
  next
    case scoped_opening
    then show ?case using no_basic_transitions_from_stop by metis
  qed
qed

private lemma no_acting_transitions_from_new_channel_stop: "\<not> \<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p"
proof
  fix \<alpha> and p
  assume "\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p"
  then show False
  proof cases
    case (scoped_acting Q\<^sub>1 Q\<^sub>2)
    from \<open>\<nu> a. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q\<^sub>1 a\<close> have "\<And>a. Q\<^sub>1 a = \<zero>"
      by (fact opening_transitions_from_new_channel_stop)
    with \<open>\<And>a. Q\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q\<^sub>2 a\<close> show ?thesis
      by (simp add: no_basic_transitions_from_stop)
  qed
qed

private lemma no_proper_transitions_from_new_channel_stop: "\<not> \<nu> a. \<zero> \<rightarrow>\<^sub>\<sharp>c"
proof
  fix c
  assume "\<nu> a. \<zero> \<rightarrow>\<^sub>\<sharp>c"
  then show False
  proof cases
    case (output_with_opening P a K)
    from \<open>\<nu> b. \<zero> \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P b\<close> have "\<And>b. P b = \<zero>"
      by (fact opening_transitions_from_new_channel_stop)
    with \<open>\<And>b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> K b\<close> show ?thesis
      by (simp add: no_proper_transitions_from_stop)
  qed (simp_all add: no_acting_transitions_from_new_channel_stop)
qed

private lemma stop_scope_redundancy: "\<nu> a. \<zero> \<sim>\<^sub>\<sharp> \<zero>"
unfolding proper.bisimilarity_def proof
  show "\<nu> a. \<zero> \<lesssim>\<^sub>\<sharp> \<zero>"
    using no_proper_transitions_from_new_channel_stop
    by (blast intro: proper.pre_bisimilarity)
next
  show "\<zero> \<lesssim>\<^sub>\<sharp> \<nu> a. \<zero>"
    using no_proper_transitions_from_stop
    by (blast intro: proper.pre_bisimilarity)
qed

lemma scope_redundancy [natural_simps]: "\<nu> a. p \<sim>\<^sub>\<sharp> p"
proof -
  have "\<nu> a. p \<sim>\<^sub>\<sharp> \<nu> a. (\<zero> \<parallel> p)"
    using basic_parallel_neutrality_left by equivalence
  also have "\<nu> a. (\<zero> \<parallel> p) \<sim>\<^sub>\<sharp> \<nu> a. \<zero> \<parallel> p"
    using parallel_scope_extension_left by equivalence
  also have "\<nu> a. \<zero> \<parallel> p \<sim>\<^sub>\<sharp> \<zero> \<parallel> p"
    using stop_scope_redundancy by equivalence
  also have "\<zero> \<parallel> p \<sim>\<^sub>\<sharp> p"
    using basic_parallel_neutrality_left by equivalence
  finally show ?thesis .
qed

end

definition tagged_new_channel :: "[nat, chan \<Rightarrow> process] \<Rightarrow> process" where
  "tagged_new_channel _ P = \<nu> a. P a"

syntax
  "_tagged_new_channel" :: "[bool list, pttrn, process] \<Rightarrow> process"
  ("(3\<langle>_\<rangle> \<nu>_./ _)" [0, 0, 100] 100)
translations
  "\<langle>t\<rangle> \<nu> a. p" \<rightleftharpoons> "CONST tagged_new_channel t (\<lambda>a. p)"

context begin

private
  lift_definition basic :: "[nat, chan \<Rightarrow> basic_behavior] \<Rightarrow> basic_behavior"
  is tagged_new_channel
  unfolding tagged_new_channel_def
  using basic_new_channel_preservation .

private
  lift_definition basic_weak :: "[nat, chan \<Rightarrow> basic_weak_behavior] \<Rightarrow> basic_weak_behavior"
  is tagged_new_channel
  unfolding tagged_new_channel_def
  using basic_weak_new_channel_preservation .

private
  lift_definition proper :: "[nat, chan \<Rightarrow> proper_behavior] \<Rightarrow> proper_behavior"
  is tagged_new_channel
  unfolding tagged_new_channel_def
  using proper_new_channel_preservation .

private
  lift_definition proper_weak :: "[nat, chan \<Rightarrow> proper_weak_behavior] \<Rightarrow> proper_weak_behavior"
  is tagged_new_channel
  unfolding tagged_new_channel_def
  using proper_weak_new_channel_preservation .

lemmas [equivalence_transfer] =
  basic.abs_eq
  basic_weak.abs_eq
  proper.abs_eq
  proper_weak.abs_eq

end

lemma tagged_parallel_scope_extension_left [natural_simps]:
  shows "\<langle>t\<rangle> \<nu> a. P a \<parallel> q \<sim>\<^sub>\<flat> \<langle>t\<rangle> \<nu> a. (P a \<parallel> q)"
  unfolding tagged_new_channel_def
  using parallel_scope_extension_left .

lemma tagged_parallel_scope_extension_right [natural_simps]:
  shows "p \<parallel> \<langle>t\<rangle> \<nu> a. Q a \<sim>\<^sub>\<flat> \<langle>t\<rangle> \<nu> a. (p \<parallel> Q a)"
  unfolding tagged_new_channel_def
  using parallel_scope_extension_right .

lemma guarded_tagged_new_channel_scope_extension [natural_simps]:
  assumes "s < t"
  shows "\<langle>t\<rangle> \<nu> b. \<langle>s\<rangle> \<nu> a. P a b \<sim>\<^sub>\<flat> \<langle>s\<rangle> \<nu> a. \<langle>t\<rangle> \<nu> b. P a b"
  unfolding tagged_new_channel_def
  using new_channel_scope_extension .

end
