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
    "\<I> p c \<Longrightarrow> superficial_basic_absorb \<I> (\<lbrace>\<tau>\<rbrace> p) c" |
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
    fix p and c
    assume "(superficial_basic_silent OO superficial_basic_absorb \<I>) p c"
    then show "\<I> p c"
      by (blast elim: superficial_basic_silent.cases superficial_basic_absorb.cases)
  next
    fix p and c
    assume "\<I> p c"
    then show "(superficial_basic_silent OO superficial_basic_absorb \<I>) p c"
      by (blast intro: silent_acting_is_silent downward_absorption)
  qed
next
  show "superficial_basic_absorb superficial_basic_silent = (=)"
  proof (intro ext, intro iffI)
    fix c and d
    assume "superficial_basic_absorb superficial_basic_silent c d"
    then show "c = d"
      by cases (simp_all add: superficial_basic_silent.simps ext)
  next
    fix c :: basic_residual and d
    assume "c = d"
    then show "superficial_basic_absorb superficial_basic_silent c d"
      by (cases c) (blast intro: silent_acting_is_silent upward_absorption)+
  qed
next
  fix \<I> and \<J>
  let ?lhs = "superficial_basic_absorb \<I> OO superficial_basic_absorb \<J>"
  let ?rhs = "superficial_basic_absorb (\<I> OO superficial_basic_absorb \<J>)"
  show "?lhs = ?rhs"
  proof (intro ext, intro iffI)
    fix c and e
    assume "(superficial_basic_absorb \<I> OO superficial_basic_absorb \<J>) c e"
    then obtain d where "superficial_basic_absorb \<I> c d" and "superficial_basic_absorb \<J> d e"
      by blast
    then show "superficial_basic_absorb (\<I> OO superficial_basic_absorb \<J>) c e"
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
    fix c and e
    assume "superficial_basic_absorb (\<I> OO superficial_basic_absorb \<J>) c e"
    then show "(superficial_basic_absorb \<I> OO superficial_basic_absorb \<J>) c e"
    proof (induction "\<I> OO superficial_basic_absorb \<J>" c e)
      case (downward_absorption p e)
      then obtain d where "\<I> p d" and "superficial_basic_absorb \<J> d e"
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
      then have "\<forall>a. \<exists>v.  \<I> (P a) (\<lbrace>\<tau>\<rbrace> v) \<and> \<J> v (\<lbrace>\<tau>\<rbrace> R a)"
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
    fix c and d
    assume "superficial_basic_absorb (\<X>\<inverse>\<inverse> OO superficial_basic_silent) d c"
    then show "(superficial_basic_absorb (\<X> OO superficial_basic_silent))\<inverse>\<inverse> d c"
    proof (induction "\<X>\<inverse>\<inverse> OO superficial_basic_silent" d c)
      case (downward_absorption q c)
      then obtain p where "\<X> p q" and "c = \<lbrace>\<tau>\<rbrace> p"
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
    fix d and c
    assume "(superficial_basic_absorb (\<X> OO superficial_basic_silent))\<inverse>\<inverse> d c"
    then have "(superficial_basic_absorb (\<X> OO superficial_basic_silent)) c d"
      by blast
    then show "superficial_basic_absorb (\<X>\<inverse>\<inverse> OO superficial_basic_silent) d c"
    proof (induction "\<X> OO superficial_basic_silent" c d)
      case (downward_absorption p d)
      then obtain q where "\<X> p q" and "d = \<lbrace>\<tau>\<rbrace> q"
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
  fix \<X> and c and d
  assume "superficial_basic_absorb (\<X> OO superficial_basic_silent) c d"
  then show "basic_lift \<X> c d"
    by (blast
      elim: superficial_basic_absorb.cases superficial_basic_silent.cases
      intro: basic_lift.intros
    )
next
  fix \<X> and c and d
  assume "basic_lift \<X> c d"
  then show "superficial_basic_absorb (\<X> OO superficial_basic_silent) c d"
    by (blast elim: basic_lift.cases intro: silent_acting_is_silent upward_absorption)
qed

interpretation superficial_basic:
  weak_transition_system superficial_basic_silent superficial_basic_absorb basic_transition
  by intro_locales

end
