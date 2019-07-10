section \<open>Diamond-Shaped Relaying Network\<close>

(* FIXME: Fill holes when bisimilarity reasoning is supported by the simplifier. *)

theory Diamond
  imports
    Chi_Calculus.Relaying
    Chi_Calculus.Proper_Weak_Transition_System
    Chi_Calculus.Basic_Weak_Transition_System
begin

abbreviation diamond where
  "diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      (* node 0 *) l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
      (* node 1 *) l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3] \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
      (* node 2 *) l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3] \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
      (* node 3 *) l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]
    )"

abbreviation split_distributors_diamond where
  "split_distributors_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      (* node 0 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
      (* node 1 *) l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
      (* node 2 *) l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
      (* node 3 *) l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
      l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"

abbreviation strongly_connected_network where
  "strongly_connected_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      (* node 0 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
      (* node 1 *) l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
      (* node 2 *) l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
      (* node 3 *) l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
      l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"

abbreviation receive_collapsed_network where
  "receive_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      (* node 0 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
      (* node 1 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
      (* node 2 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
      (* node 3 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
      l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"

abbreviation send_collapsed_network where
  "send_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      (* node 0 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      (* node 1 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      (* node 2 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      (* node 3 *) l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
      l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"

abbreviation broadcast where
  "broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      (* node 0 *) s\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>0 \<parallel>
      (* node 1 *) s\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>1 \<parallel>
      (* node 2 *) s\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>2 \<parallel>
      (* node 3 *) s\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>3
    )"

lemma diamond_distributor_split:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> split_distributors_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
proof -
  have "\<And>l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2.
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    using distributor_split sorry
  moreover have "\<And>l\<^sub>0\<^sub>1 l\<^sub>1\<^sub>3.
    \<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3"
    using distributor_split sorry
  moreover have "\<And>l\<^sub>0\<^sub>2 l\<^sub>2\<^sub>3.
    \<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3"
    using distributor_split sorry
  moreover have "\<And>l\<^sub>1\<^sub>3 l\<^sub>3\<^sub>0.
    \<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using distributor_split sorry
  moreover have "\<And>l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0.
    \<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using distributor_split sorry
  ultimately show ?thesis
    using basic_weak_bisimilarity_in_proper_weak_bisimilarity sorry
qed

lemma diamond_closure:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> split_distributors_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> strongly_connected_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
proof -
  have "\<And>l\<^sub>0\<^sub>1 l\<^sub>1\<^sub>3 l\<^sub>3\<^sub>0. l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>0\<^sub>1 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>2. l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2" 
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>2\<^sub>3. l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>0\<^sub>2 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>0\<^sub>2 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>1. l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>0\<^sub>2 l\<^sub>0\<^sub>1 l\<^sub>1\<^sub>3. l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>1\<^sub>3 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>1. l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<approx>\<^sub>\<flat> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>1\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>2\<^sub>3. l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>1\<^sub>3 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>2. l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<approx>\<^sub>\<flat> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>2. l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<approx>\<^sub>\<flat> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>2\<^sub>3 l\<^sub>0\<^sub>2 l\<^sub>0\<^sub>1. l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<approx>\<^sub>\<flat> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>2\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>1\<^sub>3. l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>1 l\<^sub>1\<^sub>3. l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3"
    by (simp add: shortcut_addition)
  moreover have "\<And>l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>2 l\<^sub>2\<^sub>3. l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    by (simp add: shortcut_addition)
  ultimately show ?thesis
    using basic_weak_bisimilarity_in_proper_weak_bisimilarity sorry
qed

lemma receive_collapse:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> strongly_connected_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> receive_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
proof -
  have "\<And>l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>1. l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<approx>\<^sub>\<flat> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1"
    by (simp add: source_switch [THEN basic.weak.bisimilarity_symmetry_rule] bidirectional_bridge_commutativity)
  moreover have "\<And>l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>2. l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<approx>\<^sub>\<flat> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2"
    by (simp add: source_switch [THEN basic.weak.bisimilarity_symmetry_rule] bidirectional_bridge_commutativity)
  moreover have "\<And>l\<^sub>3\<^sub>0 l\<^sub>1\<^sub>3. l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3"
    by (simp add: source_switch [THEN basic.weak.bisimilarity_symmetry_rule] bidirectional_bridge_commutativity)
  moreover have "\<And>l\<^sub>3\<^sub>0 l\<^sub>2\<^sub>3. l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3"
    by (simp add: source_switch [THEN basic.weak.bisimilarity_symmetry_rule] bidirectional_bridge_commutativity)
  moreover have "\<And>l\<^sub>3\<^sub>0. l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3"
    by (simp add: unidirectional_bridge_idempotency)
  ultimately show ?thesis
    using basic_weak_bisimilarity_in_proper_weak_bisimilarity sorry
qed

(* FIXME: Prove it and move to Communication.thy. *)
lemma basic_weak_multi_receive_preservation:
  assumes "\<And>x. P x \<approx>\<^sub>\<flat> Q x"
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

(* FIXME: Move to Relaying.thy. *)
lemma singleton_distribution:
  shows "a \<Rightarrow> [b] \<approx>\<^sub>\<flat> a \<rightarrow> b"
proof -
  have "\<And>x. \<Prod> c\<leftarrow>[b]. c \<triangleleft> x \<approx>\<^sub>\<flat> b \<triangleleft> x"
    sorry
  then have "a \<triangleright>\<^sup>\<infinity> x. \<Prod> c\<leftarrow>[b]. c \<triangleleft> x \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. b \<triangleleft> x"
    by (simp add: basic_weak_multi_receive_preservation)
  then show ?thesis .
qed

lemma singleton_distributor_switch:
  shows "a \<leftrightarrow> b \<parallel> c \<Rightarrow> [a] \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<rightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> c \<Rightarrow> [a] \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<rightarrow> a"
    using singleton_distribution sorry
  also have "a \<leftrightarrow> b \<parallel> c \<rightarrow> a \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> a \<triangleleft> x)"
    using context_localization sorry
  also have "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<leftrightarrow> b \<parallel> a \<triangleleft> x)"
    using context_localization sorry
  also have "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<leftrightarrow> b \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<leftrightarrow> b \<parallel> b \<triangleleft> x)"
    using send_channel_switch and basic_weak_multi_receive_preservation sorry
  also have "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<leftrightarrow> b \<parallel> b \<triangleleft> x) \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> b \<triangleleft> x)"
    using context_localization sorry
  also have "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> b \<triangleleft> x) \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<rightarrow> b"
    using context_localization sorry
  finally show ?thesis .
qed

lemma distributor_idempotency_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> b \<Rightarrow> [a,a] \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<rightarrow> a"
proof -
  have "\<currency>\<^sup>*a \<parallel> b \<Rightarrow> [a,a] \<approx>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    sorry
  also have "\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using context_localization sorry
  also have "\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using context_localization sorry
  also have "\<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x)"
  proof -
    have "\<And>x. \<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> a \<triangleleft> x"
      by (simp add: send_idempotency_under_duploss)
    then have "b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x)"
      by (simp add: basic_weak_multi_receive_preservation)
    then show ?thesis
      sorry
  qed
  also have "\<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+a \<parallel> a \<triangleleft> x)"
    using context_localization sorry
  also have "\<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+a \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. a \<triangleleft> x"
    using context_localization sorry
  finally show ?thesis .
qed

lemma two_channel_distributor_switch:
  shows "\<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<Rightarrow> [b, c] \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<rightarrow> a"
proof -
  have "\<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<Rightarrow> [b, c] \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<triangleleft> x \<parallel> c \<triangleleft> x)"
    sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<triangleleft> x \<parallel> c \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> b \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using context_localization sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> b \<triangleleft> x \<parallel> c \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> a \<parallel> b \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using context_localization sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> a \<parallel> b \<triangleleft> x \<parallel> c \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using send_channel_switch and basic_weak_multi_receive_preservation sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using context_localization sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using context_localization sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> c \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<rightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using context_localization sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<rightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using context_localization sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using send_channel_switch and basic_weak_multi_receive_preservation sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<rightarrow> a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using context_localization sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<rightarrow> a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using context_localization sorry
  also have "
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x)
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<rightarrow> a"
    using distributor_idempotency_under_duploss sorry
  finally show ?thesis .
qed

lemma send_collapse:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> receive_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> send_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
proof -
  have "\<And>l\<^sub>1\<^sub>3 l\<^sub>3\<^sub>0. l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<approx>\<^sub>\<flat> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0"
    using singleton_distributor_switch by blast
  moreover have "\<And>l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<approx>\<^sub>\<flat> l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0"
    using singleton_distributor_switch by blast
  moreover have "\<And>l\<^sub>3\<^sub>0. s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<approx>\<^sub>\<flat> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using singleton_distribution by blast
  moreover have "\<And>l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2.
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0"
    using two_channel_distributor_switch by blast
  ultimately show ?thesis
    using basic_weak_bisimilarity_in_proper_weak_bisimilarity
      and bidirectional_bridge_commutativity sorry
qed

lemma links_collapse:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> send_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
proof -
  (* Disconnect l\<^sub>0\<^sub>1 and l\<^sub>0\<^sub>2. *)
  have "\<And>l\<^sub>0\<^sub>1 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>2. l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  moreover have "\<And>l\<^sub>0\<^sub>1 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>2. l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  (* Disconnect l\<^sub>0\<^sub>1 and l\<^sub>1\<^sub>3. *)
  moreover have "\<And>l\<^sub>0\<^sub>1 l\<^sub>3\<^sub>0 l\<^sub>1\<^sub>3. l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  moreover have "\<And>l\<^sub>1\<^sub>3 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>1. l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<approx>\<^sub>\<flat> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  (* Disconnect l\<^sub>0\<^sub>1 and l\<^sub>2\<^sub>3. *)
  moreover have "\<And>l\<^sub>0\<^sub>1 l\<^sub>3\<^sub>0 l\<^sub>2\<^sub>3. l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  moreover have "\<And>l\<^sub>0\<^sub>1 l\<^sub>3\<^sub>0 l\<^sub>2\<^sub>3. l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<approx>\<^sub>\<flat> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  (* Disconnect l\<^sub>0\<^sub>2 and l\<^sub>1\<^sub>3. *)
  moreover have "\<And>l\<^sub>0\<^sub>2 l\<^sub>3\<^sub>0 l\<^sub>1\<^sub>3. l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  moreover have "\<And>l\<^sub>1\<^sub>3 l\<^sub>3\<^sub>0 l\<^sub>0\<^sub>2. l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<approx>\<^sub>\<flat> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  (* Disconnect l\<^sub>0\<^sub>2 and l\<^sub>2\<^sub>3. *)
  moreover have "\<And>l\<^sub>0\<^sub>2 l\<^sub>3\<^sub>0 l\<^sub>2\<^sub>3. l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  moreover have "\<And>l\<^sub>0\<^sub>2 l\<^sub>3\<^sub>0 l\<^sub>2\<^sub>3. l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<approx>\<^sub>\<flat> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  (* Disconnect l\<^sub>1\<^sub>3 and l\<^sub>2\<^sub>3. *)
  moreover have "\<And>l\<^sub>1\<^sub>3 l\<^sub>3\<^sub>0 l\<^sub>2\<^sub>3. l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  moreover have "\<And>l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 l\<^sub>1\<^sub>3. l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<approx>\<^sub>\<flat> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3"
    by (simp add: shortcut_addition [THEN basic.weak.bisimilarity_symmetry_rule])
  (* Remove l\<^sub>0\<^sub>1. *)
  moreover have "\<And>l\<^sub>3\<^sub>0. \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    by (simp add: duploss_detour_collapse)
  (* Remove l\<^sub>0\<^sub>2. *)
  moreover have "\<And>l\<^sub>3\<^sub>0. \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    by (simp add: duploss_detour_collapse)
  (* Remove l\<^sub>1\<^sub>3. *)
  moreover have "\<And>l\<^sub>3\<^sub>0. \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    by (simp add: duploss_detour_collapse)
  (* Remove l\<^sub>2\<^sub>3. *)
  moreover have "\<And>l\<^sub>3\<^sub>0. \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    by (simp add: duploss_detour_collapse)
  ultimately show ?thesis
    using basic_weak_bisimilarity_in_proper_weak_bisimilarity sorry
qed

lemma diamond_collapse:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
proof -
  have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> split_distributors_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using diamond_distributor_split by blast
  also have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> split_distributors_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> strongly_connected_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using diamond_closure by blast
  also have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> strongly_connected_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> receive_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using receive_collapse by blast
  also have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> receive_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> send_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using send_collapse by blast
  also have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> send_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    by (simp add: links_collapse)
  finally show ?thesis .
qed

end
