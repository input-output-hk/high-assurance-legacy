section \<open>Superficial Basic Transition System\<close>

theory Superficial_Basic_Transition_System
  imports Transition_Systems.Weak_Transition_Systems Basic_Transition_System
begin

inductive superficial_basic_silent :: "[process, basic_residual] \<Rightarrow> bool" where
  silent_acting_is_silent: "superficial_basic_silent p (\<lbrace>\<tau>\<rbrace> p)"

inductive
  superficial_basic_absorb ::
    "([process, basic_residual] \<Rightarrow> bool) \<Rightarrow> ([basic_residual, basic_residual] \<Rightarrow> bool)"
where
  downward_absorption:
    "\<I> p d \<Longrightarrow> superficial_basic_absorb \<I> (\<lbrace>\<tau>\<rbrace> p) d" |
  acting_upward_absorption:
    "\<I> p (\<lbrace>\<tau>\<rbrace> q) \<Longrightarrow> superficial_basic_absorb \<I> (\<lbrace>\<alpha>\<rbrace> p) (\<lbrace>\<alpha>\<rbrace> q)" |
  opening_upward_absorption:
    "(\<And>a. \<I> (P a) (\<lbrace>\<tau>\<rbrace> Q a)) \<Longrightarrow> superficial_basic_absorb \<I> (\<lbrace>\<nu> a\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> Q a)"

lemmas upward_absorption = acting_upward_absorption opening_upward_absorption

interpretation superficial_basic: weak_residual superficial_basic_silent superficial_basic_absorb
proof
  fix \<I> :: "[process, basic_residual] \<Rightarrow> bool" and \<J>
  assume "\<I> \<le> \<J>"
  then show "superficial_basic_absorb \<I> \<le> superficial_basic_absorb \<J>"
    by (blast elim: superficial_basic_absorb.cases intro: superficial_basic_absorb.intros)
next
  fix \<I>
  show "superficial_basic_silent OO superficial_basic_absorb \<I> = \<I>"
  proof (intro ext, intro iffI)
    fix p and d
    assume "(superficial_basic_silent OO superficial_basic_absorb \<I>) p d"
    then show "\<I> p d"
      by (blast elim: superficial_basic_silent.cases superficial_basic_absorb.cases)
  next
    fix p and d
    assume "\<I> p d"
    then show "(superficial_basic_silent OO superficial_basic_absorb \<I>) p d"
      by (blast intro: silent_acting_is_silent downward_absorption)
  qed
next
  show "superficial_basic_absorb superficial_basic_silent = (=)"
  proof (intro ext, intro iffI)
    fix d and e
    assume "superficial_basic_absorb superficial_basic_silent d e"
    then show "d = e"
      by cases (simp_all add: superficial_basic_silent.simps ext)
  next
    fix d :: basic_residual and e
    assume "d = e"
    then show "superficial_basic_absorb superficial_basic_silent d e"
      by (cases d) (blast intro: silent_acting_is_silent upward_absorption)+
  qed
next
  fix \<I> and \<J>
  let ?lhs = "superficial_basic_absorb \<I> OO superficial_basic_absorb \<J>"
  let ?rhs = "superficial_basic_absorb (\<I> OO superficial_basic_absorb \<J>)"
  show "?lhs = ?rhs"
  proof (intro ext, intro iffI)
    fix d and f
    assume "(superficial_basic_absorb \<I> OO superficial_basic_absorb \<J>) d f"
    then obtain e where "superficial_basic_absorb \<I> d e" and "superficial_basic_absorb \<J> e f"
      by blast
    then show "superficial_basic_absorb (\<I> OO superficial_basic_absorb \<J>) d f"
    proof induction
      case downward_absorption
      then show ?case
        by (blast intro: superficial_basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption \<I> p q \<alpha>)
      then show ?case
        by (blast
          elim: superficial_basic_absorb.cases
          intro: downward_absorption superficial_basic_absorb.acting_upward_absorption
        )
    next
      case (opening_upward_absorption \<I> P Q)
      then show ?case
        by (blast
          elim: superficial_basic_absorb.cases
          intro: downward_absorption superficial_basic_absorb.opening_upward_absorption
        )
    qed
  next
    fix d and f
    assume "superficial_basic_absorb (\<I> OO superficial_basic_absorb \<J>) d f"
    then show "(superficial_basic_absorb \<I> OO superficial_basic_absorb \<J>) d f"
    proof (induction "\<I> OO superficial_basic_absorb \<J>" d f)
      case (downward_absorption p f)
      then obtain e where "\<I> p e" and "superficial_basic_absorb \<J> e f"
        by blast
      then show ?case
        by (blast intro: superficial_basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption p r \<alpha>)
      then obtain q where "\<I> p (\<lbrace>\<tau>\<rbrace> q)" and "\<J> q (\<lbrace>\<tau>\<rbrace> r)"
        by (blast elim: superficial_basic_absorb.cases)
      then show ?case
        by (blast intro: superficial_basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption P R)
      then have "\<forall>a. \<exists>h.  \<I> (P a) (\<lbrace>\<tau>\<rbrace> h) \<and> \<J> h (\<lbrace>\<tau>\<rbrace> R a)"
        by (blast elim: superficial_basic_absorb.cases)
      then have "\<exists>Q. \<forall>a. \<I> (P a) (\<lbrace>\<tau>\<rbrace> Q a) \<and> \<J> (Q a) (\<lbrace>\<tau>\<rbrace> R a)"
        by (fact choice)
      then show ?case
        by (blast intro: superficial_basic_absorb.opening_upward_absorption)
    qed
  qed
next
  fix \<X>
  let ?lhs = "superficial_basic_absorb (\<X>\<inverse>\<inverse> OO superficial_basic_silent)"
  let ?rhs = "(superficial_basic_absorb (\<X> OO superficial_basic_silent))\<inverse>\<inverse>"
  show "?lhs = ?rhs"
  proof (intro ext, intro iffI)
    fix d and e
    assume "superficial_basic_absorb (\<X>\<inverse>\<inverse> OO superficial_basic_silent) e d"
    then show "(superficial_basic_absorb (\<X> OO superficial_basic_silent))\<inverse>\<inverse> e d"
    proof (induction "\<X>\<inverse>\<inverse> OO superficial_basic_silent" e d)
      case (downward_absorption q d)
      then obtain p where "\<X> p q" and "d = \<lbrace>\<tau>\<rbrace> p"
        by (blast elim: superficial_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent superficial_basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption q p \<alpha>)
      then have "\<X> p q"
        by (blast elim: superficial_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent superficial_basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption Q P)
      then have "\<And>a. \<X> (P a) (Q a)"
        by (blast elim: superficial_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent superficial_basic_absorb.opening_upward_absorption)
    qed
  next
    fix e and d
    assume "(superficial_basic_absorb (\<X> OO superficial_basic_silent))\<inverse>\<inverse> e d"
    then have "(superficial_basic_absorb (\<X> OO superficial_basic_silent)) d e"
      by blast
    then show "superficial_basic_absorb (\<X>\<inverse>\<inverse> OO superficial_basic_silent) e d"
    proof (induction "\<X> OO superficial_basic_silent" d e)
      case (downward_absorption p e)
      then obtain q where "\<X> p q" and "e = \<lbrace>\<tau>\<rbrace> q"
        by (blast elim: superficial_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent superficial_basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption p q \<alpha>)
      then have "\<X> p q"
        by (blast elim: superficial_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent superficial_basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption P Q)
      then have "\<And>a. \<X> (P a) (Q a)"
        by (blast elim: superficial_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent superficial_basic_absorb.opening_upward_absorption)
    qed
  qed
qed

lemma superficial_basic_lift_equals_basic_lift: "superficial_basic.lift = basic_lift"
proof (intro ext, intro iffI)
  fix \<X> and d and e
  assume "superficial_basic_absorb (\<X> OO superficial_basic_silent) d e"
  then show "basic_lift \<X> d e"
    by (blast
      elim: superficial_basic_absorb.cases superficial_basic_silent.cases
      intro: basic_lift.intros
    )
next
  fix \<X> and d and e
  assume "basic_lift \<X> d e"
  then show "superficial_basic_absorb (\<X> OO superficial_basic_silent) d e"
    by (blast elim: basic_lift.cases intro: silent_acting_is_silent upward_absorption)
qed

interpretation superficial_basic:
  weak_transition_system superficial_basic_silent superficial_basic_absorb basic_transition
  by intro_locales

end
