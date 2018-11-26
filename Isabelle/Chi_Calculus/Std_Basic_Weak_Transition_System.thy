section \<open>Standard Basic Weak Transition System\<close>

theory Std_Basic_Weak_Transition_System
  imports Transition_Systems.Weak_Transition_Systems Basic_Transition_System
begin

inductive std_basic_silent :: "[process, basic_residual] \<Rightarrow> bool" where
  silent_acting_is_silent: "std_basic_silent p (\<lbrace>\<tau>\<rbrace> p)"

inductive
  std_basic_absorb ::
    "([process, basic_residual] \<Rightarrow> bool) \<Rightarrow> ([basic_residual, basic_residual] \<Rightarrow> bool)"
where
  downward_absorption:
    "\<I> p d \<Longrightarrow> std_basic_absorb \<I> (\<lbrace>\<tau>\<rbrace> p) d" |
  acting_upward_absorption:
    "\<I> p (\<lbrace>\<tau>\<rbrace> q) \<Longrightarrow> std_basic_absorb \<I> (\<lbrace>\<alpha>\<rbrace> p) (\<lbrace>\<alpha>\<rbrace> q)" |
  opening_upward_absorption:
    "(\<And>a. \<I> (P a) (\<lbrace>\<tau>\<rbrace> Q a)) \<Longrightarrow> std_basic_absorb \<I> (\<lbrace>\<nu> a\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> Q a)"

lemmas upward_absorption = acting_upward_absorption opening_upward_absorption

interpretation std_basic: weak_residual std_basic_silent std_basic_absorb
proof
  fix \<I> :: "[process, basic_residual] \<Rightarrow> bool" and \<J>
  assume "\<I> \<le> \<J>"
  then show "std_basic_absorb \<I> \<le> std_basic_absorb \<J>"
    by (blast elim: std_basic_absorb.cases intro: std_basic_absorb.intros)
next
  fix \<I>
  show "std_basic_silent OO std_basic_absorb \<I> = \<I>"
  proof (intro ext, intro iffI)
    fix p and d
    assume "(std_basic_silent OO std_basic_absorb \<I>) p d"
    then show "\<I> p d"
      by (blast elim: std_basic_silent.cases std_basic_absorb.cases)
  next
    fix p and d
    assume "\<I> p d"
    then show "(std_basic_silent OO std_basic_absorb \<I>) p d"
      by (blast intro: silent_acting_is_silent downward_absorption)
  qed
next
  show "std_basic_absorb std_basic_silent = (=)"
  proof (intro ext, intro iffI)
    fix d and e
    assume "std_basic_absorb std_basic_silent d e"
    then show "d = e"
      by cases (simp_all add: std_basic_silent.simps ext)
  next
    fix d :: basic_residual and e
    assume "d = e"
    then show "std_basic_absorb std_basic_silent d e"
      by (cases d) (blast intro: silent_acting_is_silent upward_absorption)+
  qed
next
  fix \<I> and \<J>
  show "std_basic_absorb \<I> OO std_basic_absorb \<J> = std_basic_absorb (\<I> OO std_basic_absorb \<J>)"
  proof (intro ext, intro iffI)
    fix d and f
    assume "(std_basic_absorb \<I> OO std_basic_absorb \<J>) d f"
    then obtain e where "std_basic_absorb \<I> d e" and "std_basic_absorb \<J> e f"
      by blast
    then show "std_basic_absorb (\<I> OO std_basic_absorb \<J>) d f"
    proof induction
      case downward_absorption
      then show ?case by (blast intro: std_basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption \<I> p q \<alpha>)
      from `std_basic_absorb \<J> (\<lbrace>\<alpha>\<rbrace> q) f` and `\<I> p (\<lbrace>\<tau>\<rbrace> q)` show ?case
        by cases (blast intro: downward_absorption std_basic_absorb.acting_upward_absorption)+
    next
      case (opening_upward_absorption \<I> P Q)
      from `std_basic_absorb \<J> (\<lbrace>\<nu> a\<rbrace> Q a) f` and `\<And>a. \<I> (P a) (\<lbrace>\<tau>\<rbrace> Q a)` show ?case
        by cases (blast intro: downward_absorption std_basic_absorb.opening_upward_absorption)
    qed
  next
    fix d and f
    assume "std_basic_absorb (\<I> OO std_basic_absorb \<J>) d f"
    then show "(std_basic_absorb \<I> OO std_basic_absorb \<J>) d f"
    proof (induction "\<I> OO std_basic_absorb \<J>" d f)
      case (downward_absorption p f)
      then obtain e where "\<I> p e" and "std_basic_absorb \<J> e f"
        by blast
      then show ?case
        by (blast intro: std_basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption p r \<alpha>)
      then obtain q where "\<I> p (\<lbrace>\<tau>\<rbrace> q)" and "\<J> q (\<lbrace>\<tau>\<rbrace> r)"
        by (blast elim: std_basic_absorb.cases)
      then show ?case
        by (blast intro: std_basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption P R)
      then have "\<forall>a. \<exists>h.  \<I> (P a) (\<lbrace>\<tau>\<rbrace> h) \<and> \<J> h (\<lbrace>\<tau>\<rbrace> R a)"
        by (blast elim: std_basic_absorb.cases)
      then have "\<exists>Q. \<forall>a. \<I> (P a) (\<lbrace>\<tau>\<rbrace> Q a) \<and> \<J> (Q a) (\<lbrace>\<tau>\<rbrace> R a)"
        by (fact choice)
      then show ?case
        by (blast intro: std_basic_absorb.opening_upward_absorption)
    qed
  qed
next
  fix \<X>
  show "std_basic_absorb (\<X>\<inverse>\<inverse> OO std_basic_silent) = (std_basic_absorb (\<X> OO std_basic_silent))\<inverse>\<inverse>"
  proof (intro ext, intro iffI)
    fix d and e
    assume "std_basic_absorb (\<X>\<inverse>\<inverse> OO std_basic_silent) e d"
    then show "(std_basic_absorb (\<X> OO std_basic_silent))\<inverse>\<inverse> e d"
    proof (induction "\<X>\<inverse>\<inverse> OO std_basic_silent" e d)
      case (downward_absorption q d)
      then obtain p where "\<X> p q" and "d = \<lbrace>\<tau>\<rbrace> p"
        by (blast elim: std_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent std_basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption q p \<alpha>)
      then have "\<X> p q"
        by (blast elim: std_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent std_basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption Q P)
      then have "\<And>a. \<X> (P a) (Q a)"
        by (blast elim: std_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent std_basic_absorb.opening_upward_absorption)
    qed
  next
    fix e and d
    assume "(std_basic_absorb (\<X> OO std_basic_silent))\<inverse>\<inverse> e d"
    then have "(std_basic_absorb (\<X> OO std_basic_silent)) d e"
      by blast
    then show "std_basic_absorb (\<X>\<inverse>\<inverse> OO std_basic_silent) e d"
    proof (induction "\<X> OO std_basic_silent" d e)
      case (downward_absorption p e)
      then obtain q where "\<X> p q" and "e = \<lbrace>\<tau>\<rbrace> q"
        by (blast elim: std_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent std_basic_absorb.downward_absorption)
    next
      case (acting_upward_absorption p q \<alpha>)
      then have "\<X> p q"
        by (blast elim: std_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent std_basic_absorb.acting_upward_absorption)
    next
      case (opening_upward_absorption P Q)
      then have "\<And>a. \<X> (P a) (Q a)"
        by (blast elim: std_basic_silent.cases)
      then show ?case
        by (blast intro: silent_acting_is_silent std_basic_absorb.opening_upward_absorption)
    qed
  qed
qed

lemma std_basic_lift_equals_basic_lift: "std_basic.lift = basic_lift"
proof (intro ext, intro iffI)
  fix \<X> and d and e
  assume "std_basic_absorb (\<X> OO std_basic_silent) d e"
  then show "basic_lift \<X> d e"
    by (blast elim: std_basic_absorb.cases std_basic_silent.cases intro: basic_lift.intros)
next
  fix \<X> and d and e
  assume "basic_lift \<X> d e"
  then show "std_basic_absorb (\<X> OO std_basic_silent) d e"
    by (blast elim: basic_lift.cases intro: silent_acting_is_silent upward_absorption)
qed

interpretation std_basic: weak_transition_system std_basic_silent std_basic_absorb basic_transition
  by intro_locales

end
