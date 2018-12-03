section \<open>Basic Weak Transition System\<close>

theory Basic_Weak_Transition_System
  imports Transition_Systems.Weak_Transition_Systems Basic_Transition_System
begin

inductive basic_silent :: "[process, basic_residual] \<Rightarrow> bool" where
  internal_is_silent: "basic_silent p (\<lbrace>\<tau>\<rbrace> p)"

inductive
  basic_absorb :: "([process, basic_residual] \<Rightarrow> bool) \<Rightarrow> ([basic_residual, basic_residual] \<Rightarrow> bool)"
  for \<I>
where
  downward_absorption:
    "\<I> p c \<Longrightarrow> basic_absorb \<I> (\<lbrace>\<tau>\<rbrace> p) c" |
  acting_upward_absorption:
    "\<I> p (\<lbrace>\<tau>\<rbrace> q) \<Longrightarrow> basic_absorb \<I> (\<lbrace>\<alpha>\<rbrace> p) (\<lbrace>\<alpha>\<rbrace> q)" |
  opening_upward_absorption:
    "(\<And>a. \<I> (P a) (\<lbrace>\<tau>\<rbrace> Q a)) \<Longrightarrow> basic_absorb \<I> (\<lbrace>\<nu> a\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> Q a)"

lemmas upward_absorption = acting_upward_absorption opening_upward_absorption

interpretation basic: weak_residual basic_silent basic_absorb
proof
  fix \<I> :: "[process, basic_residual] \<Rightarrow> bool" and \<J>
  assume "\<I> \<le> \<J>"
  then show "basic_absorb \<I> \<le> basic_absorb \<J>"
    by (blast elim: basic_absorb.cases intro: basic_absorb.intros)
next
  fix \<I>
  show "basic_silent OO basic_absorb \<I> = \<I>"
  proof (intro ext, intro iffI)
    fix p and c
    assume "(basic_silent OO basic_absorb \<I>) p c"
    then show "\<I> p c"
      by (blast elim: basic_silent.cases basic_absorb.cases)
  next
    fix p and c
    assume "\<I> p c"
    then show "(basic_silent OO basic_absorb \<I>) p c"
      by (blast intro: internal_is_silent downward_absorption)
  qed
next
  show "basic_absorb basic_silent = (=)"
  proof (intro ext, intro iffI)
    fix c and d
    assume "basic_absorb basic_silent c d"
    then show "c = d"
      by cases (simp_all add: basic_silent.simps ext)
  next
    fix c :: basic_residual and d
    assume "c = d"
    then show "basic_absorb basic_silent c d"
      by (cases c) (blast intro: internal_is_silent upward_absorption)+
  qed
next
  fix \<I> and \<J>
  show "basic_absorb \<I> OO basic_absorb \<J> = basic_absorb (\<I> OO basic_absorb \<J>)"
  proof (intro ext, intro iffI)
    fix c and e
    assume "(basic_absorb \<I> OO basic_absorb \<J>) c e"
    then obtain d where "basic_absorb \<I> c d" and "basic_absorb \<J> d e"
      by blast
    then show "basic_absorb (\<I> OO basic_absorb \<J>) c e"
    proof induction
      case downward_absorption
      then show ?case
        by (blast intro: basic_absorb.downward_absorption)
    next
      case acting_upward_absorption
      then show ?case
        by (blast
          elim: basic_absorb.cases
          intro: downward_absorption basic_absorb.acting_upward_absorption
        )
    next
      case opening_upward_absorption
      then show ?case
        by (blast
          elim: basic_absorb.cases
          intro: downward_absorption basic_absorb.opening_upward_absorption
        )
    qed
  next
    fix c and e
    assume "basic_absorb (\<I> OO basic_absorb \<J>) c e"
    then show "(basic_absorb \<I> OO basic_absorb \<J>) c e"
    proof induction
      case (downward_absorption p e)
      then obtain d where "\<I> p d" and "basic_absorb \<J> d e"
        by blast
      then show ?case
        by (blast intro: basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption p r \<alpha>)
      then obtain q where "\<I> p (\<lbrace>\<tau>\<rbrace> q)" and "\<J> q (\<lbrace>\<tau>\<rbrace> r)"
        by (blast elim: basic_absorb.cases)
      then show ?case
        by (blast intro: basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption P R)
      then have "\<forall>a. \<exists>v.  \<I> (P a) (\<lbrace>\<tau>\<rbrace> v) \<and> \<J> v (\<lbrace>\<tau>\<rbrace> R a)"
        by (blast elim: basic_absorb.cases)
      then have "\<exists>Q. \<forall>a. \<I> (P a) (\<lbrace>\<tau>\<rbrace> Q a) \<and> \<J> (Q a) (\<lbrace>\<tau>\<rbrace> R a)"
        by (fact choice)
      then show ?case
        by (blast intro: basic_absorb.opening_upward_absorption)
    qed
  qed
next
  fix \<X>
  show "basic_absorb (\<X>\<inverse>\<inverse> OO basic_silent) = (basic_absorb (\<X> OO basic_silent))\<inverse>\<inverse>"
  proof (intro ext, intro iffI)
    fix c and d
    assume "basic_absorb (\<X>\<inverse>\<inverse> OO basic_silent) d c"
    then show "(basic_absorb (\<X> OO basic_silent))\<inverse>\<inverse> d c"
    proof induction
      case (downward_absorption q c)
      then obtain p where "\<X> p q" and "c = \<lbrace>\<tau>\<rbrace> p"
        by (blast elim: basic_silent.cases)
      then show ?case
        by (blast intro: internal_is_silent basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption q p \<alpha>)
      then have "\<X> p q"
        by (blast elim: basic_silent.cases)
      then show ?case
        by (blast intro: internal_is_silent basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption Q P)
      then have "\<And>a. \<X> (P a) (Q a)"
        by (blast elim: basic_silent.cases)
      then show ?case
        by (blast intro: internal_is_silent basic_absorb.opening_upward_absorption)
    qed
  next
    fix d and c
    assume "(basic_absorb (\<X> OO basic_silent))\<inverse>\<inverse> d c"
    then have "(basic_absorb (\<X> OO basic_silent)) c d"
      by blast
    then show "basic_absorb (\<X>\<inverse>\<inverse> OO basic_silent) d c"
    proof induction
      case (downward_absorption p d)
      then obtain q where "\<X> p q" and "d = \<lbrace>\<tau>\<rbrace> q"
        by (blast elim: basic_silent.cases)
      then show ?case
        by (blast intro: internal_is_silent basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption p q \<alpha>)
      then have "\<X> p q"
        by (blast elim: basic_silent.cases)
      then show ?case
        by (blast intro: internal_is_silent basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption P Q)
      then have "\<And>a. \<X> (P a) (Q a)"
        by (blast elim: basic_silent.cases)
      then show ?case
        by (blast intro: internal_is_silent basic_absorb.opening_upward_absorption)
    qed
  qed
qed

lemma basic_derived_lift_equals_basic_lift: "basic.lift = basic_lift"
proof (intro ext, intro iffI)
  fix \<X> and c and d
  assume "basic_absorb (\<X> OO basic_silent) c d"
  then show "basic_lift \<X> c d"
    by (blast elim: basic_absorb.cases basic_silent.cases intro: basic_lift.intros)
next
  fix \<X> and c and d
  assume "basic_lift \<X> c d"
  then show "basic_absorb (\<X> OO basic_silent) c d"
    by (blast elim: basic_lift.cases intro: internal_is_silent upward_absorption)
qed

interpretation basic: weak_transition_system basic_silent basic_absorb basic_transition
  by intro_locales

end
