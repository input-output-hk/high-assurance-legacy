section \<open>Equivalence of a Diamond-Shaped Relaying Network and a Broadcasting Network\<close>

theory Relaying_Broadcasting_Equivalence
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
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
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
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
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
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
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
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
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

lemma two_target_distributor_split:
  shows "\<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> a \<Rightarrow> [b\<^sub>1, b\<^sub>2] \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> a \<rightarrow> b\<^sub>1 \<parallel> a \<rightarrow> b\<^sub>2"
proof -
  have "\<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> a \<Rightarrow> [b\<^sub>1, b\<^sub>2] \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> [b\<^sub>1, b\<^sub>2]. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> [b\<^sub>1, b\<^sub>2]"
    using natural_simps by (simp, equivalence)
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> [b\<^sub>1, b\<^sub>2]. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> [b\<^sub>1, b\<^sub>2]. a \<rightarrow> b"
    using distributor_split by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> a \<rightarrow> b\<^sub>1 \<parallel> a \<rightarrow> b\<^sub>2"
    using natural_simps by (simp, equivalence)
  finally show ?thesis .
qed

lemma three_target_distributor_split:
  shows "
    \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> \<currency>\<^sup>?b\<^sub>3 \<parallel> a \<Rightarrow> [b\<^sub>1, b\<^sub>2, b\<^sub>3]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> \<currency>\<^sup>?b\<^sub>3 \<parallel> a \<rightarrow> b\<^sub>1 \<parallel> a \<rightarrow> b\<^sub>2 \<parallel> a \<rightarrow> b\<^sub>3"
proof -
  have "
    \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> \<currency>\<^sup>?b\<^sub>3 \<parallel> a \<Rightarrow> [b\<^sub>1, b\<^sub>2, b\<^sub>3]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> [b\<^sub>1, b\<^sub>2, b\<^sub>3]. \<currency>\<^sup>?b \<parallel> a \<Rightarrow> [b\<^sub>1, b\<^sub>2, b\<^sub>3]"
    using natural_simps by (simp, equivalence)
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> [b\<^sub>1, b\<^sub>2, b\<^sub>3]. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> [b\<^sub>1, b\<^sub>2, b\<^sub>3]. a \<rightarrow> b"
    using distributor_split by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> \<currency>\<^sup>?b\<^sub>3 \<parallel> a \<rightarrow> b\<^sub>1 \<parallel> a \<rightarrow> b\<^sub>2 \<parallel> a \<rightarrow> b\<^sub>3"
    using natural_simps by (simp, equivalence)
  finally show ?thesis .
qed

lemma diamond_distributor_split:
  shows "
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3] \<parallel>
    \<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3] \<parallel>
    \<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel>
    \<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0]
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
    \<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    \<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0" (is "?lhs \<approx>\<^sub>\<sharp> ?rhs")
proof -
  have "
    ?lhs
    \<approx>\<^sub>\<sharp>
    (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (\<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3]) \<parallel>
    (\<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3]) \<parallel>
    (\<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0]) \<parallel>
    (\<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0])"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2) \<parallel>
    (\<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (\<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (\<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    (\<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0)"
  using two_target_distributor_split and three_target_distributor_split by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp> ?rhs"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma diamond_closure:
  shows "
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
proof -
  have "
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma receive_collapse:
  shows "
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"
proof -
  have "
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3
    \<approx>\<^sub>\<flat>
    (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3"
    using source_switch by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3"
    using source_switch by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3) \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3"
    using source_switch by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3)"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3)"
    using source_switch by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  finally show ?thesis .
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
  have "\<Prod>c \<leftarrow> [b]. c \<triangleleft> x \<approx>\<^sub>\<flat> b \<triangleleft> x" for x
    using natural_simps by (simp, equivalence)
  then have "a \<triangleright>\<^sup>\<infinity> x. \<Prod>c \<leftarrow> [b]. c \<triangleleft> x \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. b \<triangleleft> x"
    by (simp add: basic_weak_multi_receive_preservation)
  then show ?thesis .
qed

lemma bridge_localization:
  shows
    "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> P x) \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
  and
    "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> P x) \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
proof -
  have "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> P x) \<approx>\<^sub>\<flat> b \<rightarrow> a \<parallel> a \<rightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> P x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> b \<rightarrow> a \<parallel> a \<rightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
    using context_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
    using natural_simps by equivalence
  finally show "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> P x) \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x" .
next
  have "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> P x) \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> a \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> P x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> a \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
    using context_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
    using natural_simps by equivalence
  finally show "a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> P x) \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x" .
qed

lemma duploss_localization:
  shows "\<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> P x) \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
proof -
  have "\<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> P x) \<approx>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?a \<parallel> P x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>?a \<parallel> P x)"
    using context_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>?a \<parallel> P x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?a \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
    using context_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma multi_receive_send_channel_switch:
  shows "a \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> c \<parallel> b \<triangleleft> x \<parallel> P x) \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> c \<parallel> c \<triangleleft> x \<parallel> P x)"
proof -
  have "a \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> c \<parallel> b \<triangleleft> x \<parallel> P x) \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. ((b \<leftrightarrow> c \<parallel> b \<triangleleft> x) \<parallel> P x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. ((b \<leftrightarrow> c \<parallel> c \<triangleleft> x) \<parallel> P x)"
    by (simp add:
          basic_weak_parallel_preservation_left
          basic_weak_multi_receive_preservation
          send_channel_switch)
    (* FIXME: Why does the following not work? 
       using send_channel_switch and basic_weak_multi_receive_preservation by equivalence *)
  also have "\<dots> \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> c \<parallel> c \<triangleleft> x \<parallel> P x)"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma distributor_idempotency_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> b \<Rightarrow> [a, a] \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<rightarrow> a"
proof -
  have "\<currency>\<^sup>*a \<parallel> b \<Rightarrow> [a, a] \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using natural_simps by (simp, equivalence)
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using duploss_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x)"
  proof -
    have "\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> a \<triangleleft> x" for x
      by (simp add: send_idempotency_under_duploss)
    then have "b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x) \<approx>\<^sub>\<flat> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> a \<triangleleft> x)"
      by (simp add: basic_weak_multi_receive_preservation)
    then show ?thesis
      by equivalence
  qed
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. a \<triangleleft> x"
    using duploss_localization by equivalence
  finally show ?thesis .
qed

lemma singleton_distributor_switch:
  shows "a \<leftrightarrow> b \<parallel> c \<Rightarrow> [a] \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<rightarrow> b"
proof -
  have "a \<leftrightarrow> b \<parallel> c \<Rightarrow> [a] \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<rightarrow> a"
    using singleton_distribution by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> a \<rightarrow> b \<parallel> a \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> \<zero>)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> a \<parallel> b \<triangleleft> x \<parallel> \<zero>)"
    using multi_receive_send_channel_switch by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> b \<rightarrow> a \<parallel> b \<triangleleft> x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<rightarrow> b"
    using bridge_localization by equivalence
  finally show ?thesis .
qed

lemma two_channel_distributor_switch:
  shows "\<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<Rightarrow> [b, c] \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<rightarrow> a"
proof -
  have "\<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<Rightarrow> [b, c] \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> c \<leftrightarrow> a \<parallel> b \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using natural_simps by (simp, equivalence)
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> c \<leftrightarrow> a \<parallel> b \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> b \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> c \<leftrightarrow> a \<parallel> b \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> b \<rightarrow> a \<parallel> b \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> c \<leftrightarrow> a \<parallel> b \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> a \<parallel> b \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> c \<leftrightarrow> a \<parallel> b \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using multi_receive_send_channel_switch by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> c \<leftrightarrow> a \<parallel> b \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (b \<rightarrow> a \<parallel> a \<rightarrow> b \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> c \<leftrightarrow> a \<parallel> b \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> b \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> c \<leftrightarrow> a \<parallel> b \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<rightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> c \<parallel> c \<rightarrow> a \<parallel> a \<triangleleft> x \<parallel> c \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<leftrightarrow> a \<parallel> c \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<leftrightarrow> a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using multi_receive_send_channel_switch by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (c \<rightarrow> a \<parallel> a \<rightarrow> c \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<rightarrow> c \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x)"
    using bridge_localization by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> \<currency>\<^sup>*a \<parallel> d \<Rightarrow> [a, a]"
    using natural_simps by (simp, equivalence)
  also have "\<dots> \<approx>\<^sub>\<flat> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> \<currency>\<^sup>*a \<parallel> d \<rightarrow> a"
    using distributor_idempotency_under_duploss by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<leftrightarrow> a \<parallel> c \<leftrightarrow> a \<parallel> d \<rightarrow> a"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma send_collapse:
  shows "
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0"
proof -
  have "
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]
    \<approx>\<^sub>\<sharp>
    (l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3]) \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    (l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"
    using singleton_distributor_switch by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3]) \<parallel>
    s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"
    using singleton_distributor_switch by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"
    using singleton_distribution by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2])"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0"
    using two_channel_distributor_switch by equivalence
  finally show ?thesis .
qed

lemma links_disconnect:
  shows "
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    \<approx>\<^sub>\<sharp>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"
proof -
  (* Disconnect l\<^sub>0\<^sub>1 and l\<^sub>0\<^sub>2. *)
  have "
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    \<approx>\<^sub>\<sharp>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1"
    using shortcut_addition by equivalence
  (* Disconnect l\<^sub>0\<^sub>1 and l\<^sub>1\<^sub>3. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1"
    using shortcut_addition by equivalence
  (* Disconnect l\<^sub>0\<^sub>1 and l\<^sub>2\<^sub>3. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1"
    using shortcut_addition by equivalence
  (* Disconnect l\<^sub>0\<^sub>2 and l\<^sub>1\<^sub>3. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    using shortcut_addition by equivalence
  (* Disconnect l\<^sub>0\<^sub>2 and l\<^sub>2\<^sub>3. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    using shortcut_addition by equivalence
  (* Disconnect l\<^sub>1\<^sub>3 and l\<^sub>2\<^sub>3. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3"
    using shortcut_addition by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma links_remove:
  shows "
    \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1) \<parallel>
    \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2) \<parallel>
    \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
    \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3)
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0"
proof -
  have "
    \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1) \<parallel>
    \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2) \<parallel>
    \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
    \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3)
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    using duploss_detour_collapse by equivalence
  also have "\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<approx>\<^sub>\<sharp> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma diamond_collapse: "
  \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
  \<approx>\<^sub>\<sharp>
  \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
proof -
  have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
      l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3] \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
      l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3] \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
      l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]
    )"
    using tagged_new_channel_def by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
      \<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3] \<parallel>
      \<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3] \<parallel>
      \<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel> \<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0]
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
      \<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
      \<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
      \<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      \<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    using diamond_distributor_split by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> split_distributors_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3
    )"
    using diamond_closure by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> strongly_connected_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"
    using receive_collapse by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> receive_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel>
      l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel>
      s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel>
      l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel>
      s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    using send_collapse by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> send_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"
    using links_disconnect by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1) \<parallel>
      \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2) \<parallel>
      \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
      \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3) \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> (
      \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1) \<parallel>
      \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2) \<parallel>
      \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
      \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3)) \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    using natural_simps unfolding tagged_new_channel_def by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0 \<parallel> s\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1 \<parallel> s\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2 \<parallel> s\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3 \<parallel> s\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    using links_remove by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using natural_simps by equivalence
  finally show ?thesis .
qed

end
