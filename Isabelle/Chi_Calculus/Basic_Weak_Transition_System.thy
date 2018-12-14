section \<open>Basic Weak Transition System\<close>

theory Basic_Weak_Transition_System
  imports
    Transition_Systems.Std_Weak_Residuals
    Transition_Systems.Weak_Transition_Systems
    Basic_Transition_System
begin

inductive basic_silent :: "[process, basic_residual] \<Rightarrow> bool" where
  basic_internal_is_silent: "basic_silent p (\<lbrace>\<tau>\<rbrace> p)"

interpretation basic: std_weak_residual basic_lift basic_silent
proof
  show "basic_silent OO basic_silent\<inverse>\<inverse> = (=)"
    by (blast elim: basic_silent.cases intro: basic_silent.intros)
next
  show "basic_silent\<inverse>\<inverse> OO basic_silent \<le> (=)"
    by (blast elim: basic_silent.cases)
next
  fix \<X>
  show "\<X> OO basic_silent = basic_silent OO basic_lift \<X>"
  proof (intro ext, intro iffI)
    fix p and c
    assume "(\<X> OO basic_silent) p c"
    then show "(basic_silent OO basic_lift \<X>) p c"
      by (blast elim: basic_silent.cases intro: basic_silent.intros acting_lift)
  next
    fix p and c
    assume "(basic_silent OO basic_lift \<X>) p c"
    then show "(\<X> OO basic_silent) p c"
      by (blast elim: basic_silent.cases basic_lift.cases intro: basic_silent.intros)
  qed
qed

interpretation basic: weak_transition_system basic_silent basic.absorb basic_transition
  by intro_locales

end
