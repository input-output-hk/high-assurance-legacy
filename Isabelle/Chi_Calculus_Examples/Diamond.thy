section \<open>Diamond-Shaped Relaying Network\<close>

theory Diamond
  imports Relaying Chi_Calculus.Proper_Weak_Transition_System Chi_Calculus.Basic_Weak_Transition_System
begin

(* FIXME: Move to `Basic_Weak_Transition_System` and `Proper_Weak_Transition_System`, respectively. *)
lemma basic_strong_bisimilarity_in_weak_bisimilarity': "p \<sim>\<^sub>\<flat> q \<Longrightarrow> p \<approx>\<^sub>\<flat> q" sorry
lemma proper_strong_bisimilarity_in_weak_bisimilarity': "p \<sim>\<^sub>\<sharp> q \<Longrightarrow> p \<approx>\<^sub>\<sharp> q" sorry

(* FIXME: Use Wolfgang's idea for the proof. *)
lemma basic_weak_parallel_swap: "init \<parallel> p \<parallel> mid \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> init \<parallel> q \<parallel> mid \<parallel> p \<parallel> tail"
proof -
  have "mid \<parallel> q \<approx>\<^sub>\<flat> q \<parallel> mid"
    by (simp add: basic_weak_parallel_commutativity)
  then have "p \<parallel> (mid \<parallel> q) \<approx>\<^sub>\<flat> p \<parallel> (q \<parallel> mid)"
    using basic_weak_parallel_preservation_right by blast
  moreover have "p \<parallel> q \<approx>\<^sub>\<flat> q \<parallel> p"
    by (simp add: basic_weak_parallel_commutativity)
  then have "(p \<parallel> q) \<parallel> mid \<approx>\<^sub>\<flat> (q \<parallel> p) \<parallel> mid"
    using basic_weak_parallel_preservation_left by blast
  ultimately have "p \<parallel> mid \<parallel> q \<approx>\<^sub>\<flat> q \<parallel> p \<parallel> mid"
    by (metis (no_types, lifting) basic.weak.bisimilarity_transitivity_rule basic_weak_parallel_associativity)
  moreover have "p \<parallel> mid \<approx>\<^sub>\<flat> mid \<parallel> p"
    by (simp add: basic_weak_parallel_commutativity)
  then have "q \<parallel> (p \<parallel> mid) \<approx>\<^sub>\<flat> q \<parallel> (mid \<parallel> p)"
    using basic_weak_parallel_preservation_right by blast
  ultimately have "p \<parallel> mid \<parallel> q \<approx>\<^sub>\<flat> q \<parallel> mid \<parallel> p"
    using basic.weak.bisimilarity_transitivity_rule by blast
  then have "init \<parallel> p \<parallel> mid \<parallel> q \<approx>\<^sub>\<flat> init \<parallel> q \<parallel> mid \<parallel> p"
    using basic_weak_parallel_preservation_right by blast
  then have parenthesized_theory: "(init \<parallel> p \<parallel> mid \<parallel> q) \<parallel> tail \<approx>\<^sub>\<flat> (init \<parallel> q \<parallel> mid \<parallel> p) \<parallel> tail"
    using basic_weak_parallel_preservation_left by blast
  then have "init \<parallel> p \<parallel> mid \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> init \<parallel> q \<parallel> mid \<parallel> p \<parallel> tail"
    sorry (* TODO: Prove it *)
  then show ?thesis
    by blast
qed

lemma basic_weak_parallel_swap_neighbors: "init \<parallel> p \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> init \<parallel> q \<parallel> p \<parallel> tail"
proof -
  have "init \<parallel> p \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> init \<parallel> p \<parallel> \<zero> \<parallel> q \<parallel> tail"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_unit_left)
  also have "init \<parallel> p \<parallel> \<zero> \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> init \<parallel> q \<parallel> \<zero> \<parallel> p \<parallel> tail"
    by (simp add: basic_weak_parallel_swap)
  finally show ?thesis
    by (smt basic.weak.bisimilarity_transitivity_rule basic_weak_parallel_associativity basic_weak_parallel_commutativity basic_weak_parallel_unit_left) (* TODO: Find a nicer proof. *)
qed

lemma basic_weak_parallel_swap_last: "init \<parallel> p \<parallel> mid \<parallel> q \<approx>\<^sub>\<flat> init \<parallel> q \<parallel> mid \<parallel> p"
proof -
  have "init \<parallel> p \<parallel> mid \<parallel> q \<approx>\<^sub>\<flat> init \<parallel> p \<parallel> mid \<parallel> q \<parallel> \<zero>"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_unit_right)
  also have "init \<parallel> p \<parallel> mid \<parallel> q \<parallel> \<zero> \<approx>\<^sub>\<flat> init \<parallel> q \<parallel> mid \<parallel> p \<parallel> \<zero>"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  finally show ?thesis
    by (smt basic.weak.bisimilarity_transitivity_rule basic_weak_parallel_preservation_right basic_weak_parallel_unit_right) (* TODO: Find a nicer proof. *)
qed

lemma basic_weak_parallel_swap_first: "p \<parallel> mid \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> q \<parallel> mid \<parallel> p \<parallel> tail"
proof -
  have "p \<parallel> mid \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> \<zero> \<parallel> p \<parallel> mid \<parallel> q \<parallel> tail"
    by (simp add: basic_weak_parallel_unit_left)
  also have "\<zero> \<parallel> p \<parallel> mid \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> \<zero> \<parallel> q \<parallel> mid \<parallel> p \<parallel> tail"
    by (simp add: basic_weak_parallel_swap)
  finally show ?thesis
    using basic.weak.bisimilarity_transitivity_rule and basic_weak_parallel_unit_left by blast
qed

lemma basic_weak_parallel_swap_first_pair: "p \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> q \<parallel> p \<parallel> tail"
proof -
  have "p \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> \<zero> \<parallel> p \<parallel> q \<parallel> tail"
    by (simp add: basic_weak_parallel_unit_left)
  also have "\<zero> \<parallel> p \<parallel> q \<parallel> tail \<approx>\<^sub>\<flat> \<zero> \<parallel> q \<parallel> p \<parallel> tail"
    by (simp add: basic_weak_parallel_swap_neighbors)
  finally show ?thesis
    using basic.weak.bisimilarity_transitivity_rule and basic_weak_parallel_unit_left by blast
qed

abbreviation diamond :: "[chan, chan, chan, chan, chan] \<Rightarrow> process" where
  "diamond a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<equiv>
    \<currency>\<^sup>*a\<^sub>0 \<parallel>
    \<nu> a\<^sub>1 a\<^sub>2 a\<^sub>3. (
      \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
      a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
      a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    )"

abbreviation big_headed_diamond :: "[chan, chan, chan, chan, chan] \<Rightarrow> process" where
  "big_headed_diamond a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<equiv>
    \<currency>\<^sup>*a\<^sub>0 \<parallel>
    \<nu> a\<^sub>1 a\<^sub>2 a\<^sub>3. (
      \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
      a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
      a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    )"

abbreviation big_headed_chain :: "[chan, chan, chan, chan, chan] \<Rightarrow> process" where
  "big_headed_chain a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<equiv>
    \<currency>\<^sup>*a\<^sub>0 \<parallel>
    \<nu> a\<^sub>1 a\<^sub>2 a\<^sub>3. (
      \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
                a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
      a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    )"

(* Step 1: Convert a `diamond` into a `big_headed_diamond`. *)

context
begin

private lemma pre_move_b\<^sub>1_permutation: "
  a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1"
proof -
  have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_swap_first_pair)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_swap_neighbors by blast
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_preservation_right basic_weak_parallel_swap_neighbors by blast
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_preservation_right basic_weak_parallel_swap_neighbors by blast
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_preservation_right basic_weak_parallel_swap by blast
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap_last)
  finally show ?thesis
    by simp
qed

private lemma move_b\<^sub>1_permutation: "
  a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1
  \<approx>\<^sub>\<flat>
  a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2"
proof -
  have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1"
    using basic_weak_parallel_swap_first_pair by blast
  also have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1"
    by (simp add: basic_weak_parallel_swap_neighbors)
  also have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap_neighbors)
  also have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1"
    using basic_weak_parallel_preservation_right basic_weak_parallel_swap by blast
  also have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  also have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap_last)
  also have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2"
    by (simp add: basic_weak_parallel_commutativity basic_weak_parallel_preservation_right)
  finally show ?thesis
    by blast
qed

private lemma move_b\<^sub>2_permutation: "
  a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2
  \<approx>\<^sub>\<flat>
  a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3"
proof -
  have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2"
    using basic_weak_parallel_swap_first_pair by blast
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2"
    by (simp add: basic_weak_parallel_swap_neighbors)
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap_last)
  finally show ?thesis
    by blast
qed

private lemma move_b\<^sub>3_1_permutation: "
  a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3
  \<approx>\<^sub>\<flat>
  a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3"
proof -
  have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_preservation_right basic_weak_parallel_swap_neighbors by blast
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_preservation_right basic_weak_parallel_swap_neighbors by blast
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap_neighbors)
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap_neighbors)
  finally show ?thesis
    by blast
qed

private lemma move_b\<^sub>3_2_permutation: "
  a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
proof -
  have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    sorry (* TODO: Prove it *)
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_swap_first by blast
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    sorry (* TODO: Prove it *)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_swap by blast
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_associativity basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    using basic_weak_parallel_preservation_right basic_weak_parallel_swap by blast
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    sorry (* TODO: Prove it *)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_associativity basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  finally show ?thesis
    by blast
qed

private lemma diamond_output_links_move: "
  a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
proof -
  have move_b\<^sub>1: "a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<approx>\<^sub>\<flat> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1"
    by (simp add: source_shift)
  have move_b\<^sub>2: "a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<approx>\<^sub>\<flat> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2"
    by (simp add: source_shift)
  have move_b\<^sub>3_1: "a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<approx>\<^sub>\<flat> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3"
    by (simp add: source_shift)
  have move_b\<^sub>3_2: "a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3 \<approx>\<^sub>\<flat> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: source_shift)
  have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1"
    by (simp add: pre_move_b\<^sub>1_permutation)
  also from move_b\<^sub>1 have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2"
    by (simp add: move_b\<^sub>1_permutation)
  also from move_b\<^sub>2 have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3"
    by (simp add: move_b\<^sub>2_permutation)
  also from move_b\<^sub>3_1 have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3"
    by (simp add: move_b\<^sub>3_1_permutation)
  also from move_b\<^sub>3_2 have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: move_b\<^sub>3_2_permutation)
  finally show ?thesis
    by blast
qed

lemma diamond_and_big_headed_diamond_equivalence: "diamond a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<flat> big_headed_diamond a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3"
proof -
  have "\<And>a\<^sub>1 a\<^sub>2 a\<^sub>3.
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: diamond_output_links_move)
  then have "\<And>a\<^sub>1 a\<^sub>2 a\<^sub>3.
    \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
    a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
    a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right)
  then have "
    \<nu> a\<^sub>1 a\<^sub>2 a\<^sub>3. (
      \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
      a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
      a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> b\<^sub>3
    )
    \<approx>\<^sub>\<flat>
    \<nu> a\<^sub>1 a\<^sub>2 a\<^sub>3. (
      \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
      a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
      a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    )"
    by (simp add: basic_weak_new_channel_preservation)
  then show ?thesis
    by (simp add: basic_weak_parallel_preservation)
qed

end

(* Step 2: Convert a `big_headed_diamond` into a `big_headed_chain`. *)

context
begin

private lemma pre_move_1_permutation: "
  a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1"
proof -
  have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> (a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    sorry (* TODO: Prove it. *)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> (a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    \<zero> \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> (a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_unit_left)
  also have "
    \<zero> \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> (a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    \<zero> \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> (a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_swap_last)
  also have "
    \<zero> \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> (a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> (a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_unit_left)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> (a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1"
    sorry (* TODO: Prove it. *)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1"
    sorry (* TODO: Prove it. *)
  finally show ?thesis
    by blast
qed

private lemma pre_move_2_permutation: "
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0"
proof -
  have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0"
    sorry (* TODO: Prove it. *)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0"
    sorry (* TODO: Prove it. *)
  finally show ?thesis
    by blast
qed

private lemma pre_drop_1_permutation: "
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0"
proof -
  have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0"
    sorry (* TODO: Prove it. *)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0"
    by (simp add: basic_weak_parallel_swap)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0"
    sorry (* TODO: Prove it. *)
  finally show ?thesis
    by blast
qed

private lemma pre_move_3_permutation: "
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1"
  by (simp add: basic_weak_parallel_commutativity basic_weak_parallel_preservation_right)

private lemma pre_move_4_permutation: "
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1"
proof -
  have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1"
    sorry (* TODO: Prove it. *)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_swap)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1"
    sorry (* TODO: Prove it. *)
  finally show ?thesis
    by simp
qed

private lemma pre_drop_2_permutation: "
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1"
proof -
  have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_associativity basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_associativity basic_weak_parallel_preservation_right)
  finally show ?thesis
    by simp
qed

private lemma post_drop_2_permutation: "
  a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
proof -
  have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3"
    by (simp add: basic_weak_parallel_swap_first_pair)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3"
    sorry (* TODO: Prove it. *)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_swap_last)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_left basic_weak_parallel_preservation_right basic_weak_parallel_swap_first_pair)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation basic_weak_parallel_swap_neighbors)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_commutativity basic_weak_parallel_preservation_left basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> (a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3" 
    sorry (* TODO: Prove it. *)
  finally show ?thesis
    by simp
qed

private lemma big_headed_diamond_inner_links_move: "
  a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
  \<approx>\<^sub>\<flat>
  a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
proof -
  have move_1: "a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> a\<^sub>0 \<approx>\<^sub>\<flat> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0"
    by (simp add: source_shift)
  have move_2: "a\<^sub>3 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0 \<approx>\<^sub>\<flat> a\<^sub>3 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0"
    by (simp add: source_shift)
  have drop_1: "a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0 \<approx>\<^sub>\<flat> a\<^sub>0 \<leftrightarrow> a\<^sub>2"
    by (simp add: backward_link_absorption basic_strong_bisimilarity_in_weak_bisimilarity')
  have move_3: "a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<approx>\<^sub>\<flat> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1"
    by (simp add: source_shift)
  have move_4: "a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1 \<approx>\<^sub>\<flat> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1"
    by (simp add: source_shift)
  have drop_2: "a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1 \<approx>\<^sub>\<flat> a\<^sub>1 \<leftrightarrow> a\<^sub>3"
    by (simp add: backward_link_absorption basic_strong_bisimilarity_in_weak_bisimilarity')
  have "
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1"
    by (simp add: pre_move_1_permutation)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> a\<^sub>0"
    by (simp add: basic_weak_parallel_preservation_right basic_weak_parallel_swap_neighbors)
  also from move_1 have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>1 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0"
    by (simp add: pre_move_2_permutation)
  also from move_2 have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0" 
    by (simp add: basic_weak_parallel_preservation_right source_shift)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0"
    by (simp add: pre_drop_1_permutation)
  also from drop_1 have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>0
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1"
    by (simp add: pre_move_3_permutation)
  also from move_3 have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1"
    by (simp add: pre_move_4_permutation)
  also from move_4 have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1"
    by (simp add: pre_drop_2_permutation)
  also from drop_2 have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>3 \<rightarrow> a\<^sub>1
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right)
  also have "
    a\<^sub>0 \<rightarrow> b\<^sub>3 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: post_drop_2_permutation)
  finally show ?thesis
    by blast
qed

lemma big_headed_diamond_and_big_headed_chain_equivalence: "big_headed_diamond a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<flat> big_headed_chain a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3"
proof -
  have "\<And>a\<^sub>1 a\<^sub>2 a\<^sub>3.
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: big_headed_diamond_inner_links_move)
  then have "\<And>a\<^sub>1 a\<^sub>2 a\<^sub>3.
    \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
    a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
    a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
    a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
    a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    by (simp add: basic_weak_parallel_preservation_right)
  then have "
    \<nu> a\<^sub>1 a\<^sub>2 a\<^sub>3. (
      \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
      a\<^sub>0 \<leftrightarrow> a\<^sub>1 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
      a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    )
    \<approx>\<^sub>\<flat>
    \<nu> a\<^sub>1 a\<^sub>2 a\<^sub>3. (
      \<currency>\<^sup>*a\<^sub>1 \<parallel> \<currency>\<^sup>*a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<parallel>
      a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
      a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    )"
    by (simp add: basic_weak_new_channel_preservation)
  then show ?thesis
    by (simp add: basic_weak_parallel_preservation)
qed

end

(* Step 3: Collapse a `big_headed_chain` into a single, big-headed node. *)

context
begin

private lemma loss_and_duplication_idempotency_aux: "\<currency>\<^sup>*a \<parallel> p \<parallel> \<currency>\<^sup>*a \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a \<parallel> p"
proof -
  have "\<currency>\<^sup>*a \<parallel> p \<parallel> \<currency>\<^sup>*a \<approx>\<^sub>\<sharp> (\<currency>\<^sup>*a \<parallel> \<currency>\<^sup>*a) \<parallel> p"
    by (metis (no_types, lifting) proper.weak.bisimilarity_transitivity_rule proper_weak_parallel_associativity proper_weak_parallel_commutativity)
  also have "(\<currency>\<^sup>*a \<parallel> \<currency>\<^sup>*a) \<parallel> p \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a \<parallel> p"
    by (simp add: basic_bisimilarity_in_proper_bisimilarity_rule loss_and_duplication_idempotency proper_parallel_preservation_left proper_strong_bisimilarity_in_weak_bisimilarity')
  finally show "\<currency>\<^sup>*a \<parallel> p \<parallel> \<currency>\<^sup>*a \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a \<parallel> p"
    by simp
qed

lemma big_headed_chain_and_big_headed_node_equivalence: "big_headed_chain a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
proof -
  have "
    big_headed_chain a\<^sub>0 b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*a\<^sub>0 \<parallel>
    \<nu> a\<^sub>2. (
      \<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel>
      \<nu> a\<^sub>3. (
        \<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
        \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3))) \<parallel>
    a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    sorry (* TODO: Prove it (basically use scope redundancy). *)
  moreover have "
    \<currency>\<^sup>*a\<^sub>0 \<parallel>
    \<nu> a\<^sub>2. (
      \<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel>
      \<nu> a\<^sub>3. (
        \<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel>
        \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3))) \<parallel>
    a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*a\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
  proof -
    have "
      \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3))))
      \<approx>\<^sub>\<sharp>
      \<currency>\<^sup>*a\<^sub>0"
    proof -
      have "
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3))))
        \<approx>\<^sub>\<sharp>
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<currency>\<^sup>*a\<^sub>3)))"
      proof -
        have "\<And>a\<^sub>1 a\<^sub>2 a\<^sub>3. \<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3 \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>3 \<leftrightarrow> a\<^sub>1"
          by (simp add: proper_weak_parallel_commutativity proper_weak_parallel_preservation_right)
        then have "\<And>a\<^sub>2 a\<^sub>3. \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3) \<approx>\<^sub>\<sharp> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>3 \<leftrightarrow> a\<^sub>1)"
          by (simp add: proper_weak_new_channel_preservation)
        also have "\<And>a\<^sub>2 a\<^sub>3. \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>3 \<leftrightarrow> a\<^sub>1) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>3"
          by (simp add: dead_end_collapse)
        finally have "\<And>a\<^sub>2 a\<^sub>3. \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>3"
          by blast
        then have "\<And>a\<^sub>2 a\<^sub>3. \<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<currency>\<^sup>*a\<^sub>3"
          by (simp add: proper_weak_parallel_preservation_right)
        then have "\<And>a\<^sub>2. \<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3)) \<approx>\<^sub>\<sharp> \<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<currency>\<^sup>*a\<^sub>3)"
          by (simp add: proper_weak_new_channel_preservation)
        then have "\<And>a\<^sub>2. \<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> \<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3)) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> \<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<currency>\<^sup>*a\<^sub>3)"
          by (simp add: proper_weak_parallel_preservation_right)
        then show ?thesis
          by (simp add: proper_weak_new_channel_preservation)
      qed
      also have "
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<currency>\<^sup>*a\<^sub>3)))
        \<approx>\<^sub>\<sharp>
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3)))"
      proof -
        have "\<And>a\<^sub>2 a\<^sub>3. \<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<currency>\<^sup>*a\<^sub>3 \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3"
          by (simp add: loss_and_duplication_idempotency_aux)
        then have "\<And>a\<^sub>2. \<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<currency>\<^sup>*a\<^sub>3)) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3))"
          by (simp add: proper_weak_new_channel_preservation proper_weak_parallel_preservation_right)
        then show ?thesis
          by (simp add: proper_weak_new_channel_preservation)
      qed
      also have "
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3)))
        \<approx>\<^sub>\<sharp>
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>2)"
        by (simp add: dead_end_collapse proper_weak_new_channel_preservation proper_weak_parallel_preservation_right)
      also have "
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> \<currency>\<^sup>*a\<^sub>2)
        \<approx>\<^sub>\<sharp>
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2)"
        by (simp add: loss_and_duplication_idempotency_aux proper_weak_new_channel_preservation)
      also have "
        \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2)
        \<approx>\<^sub>\<sharp>
        \<currency>\<^sup>*a\<^sub>0"
        using dead_end_collapse by blast
      finally show ?thesis
        by simp
    qed
    then have fact1: "
      \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3)))) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
      \<approx>\<^sub>\<sharp>
      \<currency>\<^sup>*a\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
      by (simp add: proper_weak_parallel_preservation_left)
    then have "
      \<currency>\<^sup>*a\<^sub>0 \<parallel> \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3)))) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
      \<approx>\<^sub>\<sharp>
      \<currency>\<^sup>*a\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
    proof -
      have "
        \<currency>\<^sup>*a\<^sub>0 \<parallel> \<nu> a\<^sub>2. (\<currency>\<^sup>*a\<^sub>2 \<parallel> a\<^sub>0 \<leftrightarrow> a\<^sub>2 \<parallel> (\<nu> a\<^sub>3. (\<currency>\<^sup>*a\<^sub>3 \<parallel> a\<^sub>2 \<leftrightarrow> a\<^sub>3 \<parallel> \<nu> a\<^sub>1. (\<currency>\<^sup>*a\<^sub>1 \<parallel> a\<^sub>1 \<leftrightarrow> a\<^sub>3)))) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3
        \<approx>\<^sub>\<sharp>
        \<currency>\<^sup>*a\<^sub>0 \<parallel> \<currency>\<^sup>*a\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
        by (simp add: fact1 proper_weak_parallel_preservation_right)
      moreover have "\<currency>\<^sup>*a\<^sub>0 \<parallel> \<currency>\<^sup>*a\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3 \<approx>\<^sub>\<sharp> (\<currency>\<^sup>*a\<^sub>0 \<parallel> \<currency>\<^sup>*a\<^sub>0) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
        by (simp add: proper_weak_parallel_associativity)
      also have "(\<currency>\<^sup>*a\<^sub>0 \<parallel> \<currency>\<^sup>*a\<^sub>0) \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3 \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>1 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>2 \<parallel> a\<^sub>0 \<rightarrow> b\<^sub>3"
        by (simp add: basic_bisimilarity_in_proper_bisimilarity_rule basic_parallel_preservation_left loss_and_duplication_idempotency proper_strong_bisimilarity_in_weak_bisimilarity')
      ultimately show ?thesis
        using proper.weak.bisimilarity_transitivity_rule by blast
    qed
    then show ?thesis
      by simp
  qed
  ultimately show ?thesis
    using proper.weak.bisimilarity_transitivity_rule by blast
qed

end

lemma diamond_collapse: "diamond a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a \<parallel> a \<rightarrow> b\<^sub>0 \<parallel> a \<rightarrow> b\<^sub>1 \<parallel> a \<rightarrow> b\<^sub>2 \<parallel> a \<rightarrow> b\<^sub>3"
proof -
  have "diamond a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<flat> big_headed_diamond a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3"
    by (simp add: diamond_and_big_headed_diamond_equivalence)
  also have "big_headed_diamond a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<flat> big_headed_chain a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3"
    by (simp add: big_headed_diamond_and_big_headed_chain_equivalence)
  finally have "diamond a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<flat> big_headed_chain a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3"
    by blast
  then have "diamond a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<sharp> big_headed_chain a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3"
    sorry (* TODO: Prove it. *)
  moreover have "big_headed_chain a b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a \<parallel> a \<rightarrow> b\<^sub>0 \<parallel> a \<rightarrow> b\<^sub>1 \<parallel> a \<rightarrow> b\<^sub>2 \<parallel> a \<rightarrow> b\<^sub>3"
    by (simp add: big_headed_chain_and_big_headed_node_equivalence)
  ultimately show ?thesis
    using proper.weak.bisimilarity_transitivity_rule by blast
qed

end
