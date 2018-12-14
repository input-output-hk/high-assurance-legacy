section \<open>Proper Weak Transition System\<close>

theory Proper_Weak_Transition_System
  imports
    Transition_Systems.Std_Weak_Residuals
    Transition_Systems.Weak_Transition_Systems
    Proper_Transition_System
begin

inductive proper_silent :: "[process, proper_residual] \<Rightarrow> bool" where
  proper_internal_is_silent: "proper_silent p (\<lparr>\<tau>\<rparr> p)"

interpretation proper: std_weak_residual proper_lift proper_silent
proof
  show "proper_silent OO proper_silent\<inverse>\<inverse> = (=)"
    by (blast elim: proper_silent.cases intro: proper_silent.intros)
next
  show "proper_silent\<inverse>\<inverse> OO proper_silent \<le> (=)"
    by (blast elim: proper_silent.cases)
next
  fix \<X>
  show "\<X> OO proper_silent = proper_silent OO proper_lift \<X>"
  proof (intro ext, intro iffI)
    fix p and c
    assume "(\<X> OO proper_silent) p c"
    then show "(proper_silent OO proper_lift \<X>) p c"
      by (blast elim: proper_silent.cases intro: proper_silent.intros simple_lift)
  next
    fix p and c
    assume "(proper_silent OO proper_lift \<X>) p c"
    then show "(\<X> OO proper_silent) p c"
      by (blast elim: proper_silent.cases proper_lift.cases intro: proper_silent.intros)
  qed
qed

interpretation proper: weak_transition_system proper_silent proper.absorb proper_transition
  by intro_locales

end
