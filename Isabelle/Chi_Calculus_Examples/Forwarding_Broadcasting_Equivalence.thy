section \<open>Equivalence of a Diamond-Shaped Forwarding Network and a Broadcasting Network\<close>

theory Forwarding_Broadcasting_Equivalence
  imports
    Chi_Calculus.Communication
    Chi_Calculus.Proper_Weak_Transition_System
    Chi_Calculus.Basic_Weak_Transition_System
begin

abbreviation diamond where
  "diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<comment> \<open>node 0\<close> \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0]) \<parallel>
      \<comment> \<open>node 1\<close> \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1]) \<parallel>
      \<comment> \<open>node 2\<close> \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2]) \<parallel>
      \<comment> \<open>node 3\<close> \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3])
    )"

abbreviation sidetrack_addition_diamond where
  "sidetrack_addition_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<comment> \<open>node 0\<close> \<nu> ib\<^sub>0 ob\<^sub>0. (
          s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<comment> \<open>node 1\<close> \<nu> ib\<^sub>1 ob\<^sub>1. (
          s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<comment> \<open>node 2\<close> \<nu> ib\<^sub>2 ob\<^sub>2. (
          s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<comment> \<open>node 3\<close> \<nu> ib\<^sub>3 ob\<^sub>3. (
          s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"

abbreviation buffered_relaying_diamond where
  "buffered_relaying_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<comment> \<open>node 0\<close> \<nu> ib\<^sub>0 ob\<^sub>0. (
          s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<comment> \<open>node 1\<close> \<nu> ib\<^sub>1 ob\<^sub>1. (
          s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<comment> \<open>node 2\<close> \<nu> ib\<^sub>2 ob\<^sub>2. (
          s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<comment> \<open>node 3\<close> \<nu> ib\<^sub>3 ob\<^sub>3. (
          s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"

abbreviation strongly_connected_network where
  "strongly_connected_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<comment> \<open>node 0\<close> \<nu> ib\<^sub>0 ob\<^sub>0. (
        s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<comment> \<open>node 1\<close> \<nu> ib\<^sub>1 ob\<^sub>1. (
        s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<comment> \<open>node 2\<close> \<nu> ib\<^sub>2 ob\<^sub>2. (
        s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<comment> \<open>node 3\<close> \<nu> ib\<^sub>3 ob\<^sub>3. (
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"

abbreviation receive_collapsed_network where
  "receive_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<comment> \<open>node 0\<close> \<nu> ib\<^sub>0 ob\<^sub>0. (
          s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<comment> \<open>node 1\<close> \<nu> ib\<^sub>1 ob\<^sub>1. (
          s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<comment> \<open>node 2\<close> \<nu> ib\<^sub>2 ob\<^sub>2. (
          s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<comment> \<open>node 3\<close> \<nu> ib\<^sub>3 ob\<^sub>3. (
          s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"

abbreviation send_collapsed_network where
  "send_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<comment> \<open>node 0\<close> \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<comment> \<open>node 1\<close> \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<comment> \<open>node 2\<close> \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<comment> \<open>node 3\<close> \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"

abbreviation buffered_broadcast where
  "buffered_broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      \<comment> \<open>node 0\<close> \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<comment> \<open>node 1\<close> \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<comment> \<open>node 2\<close> \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<comment> \<open>node 3\<close> \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"

abbreviation broadcast where
  "broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      \<comment> \<open>node 0\<close> s\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>0 \<parallel>
      \<comment> \<open>node 1\<close> s\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>1 \<parallel>
      \<comment> \<open>node 2\<close> s\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>2 \<parallel>
      \<comment> \<open>node 3\<close> s\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>3
    )"

lemma diamond_sidetrack_addition:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel>
    ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3"
proof -
  have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3]
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel>
    \<Prod>b \<leftarrow> [r\<^sub>0]. \<currency>\<^sup>?b \<parallel> ib\<^sub>0 \<Rightarrow> [ob\<^sub>0, r\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel>
    \<Prod>b \<leftarrow> [r\<^sub>0]. \<currency>\<^sup>?b \<parallel> ib\<^sub>0 \<Rightarrow> [ob\<^sub>0, r\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0"
    using sidetrack_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
    ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> \<Prod>b \<leftarrow> [r\<^sub>1]. \<currency>\<^sup>?b \<parallel> ib\<^sub>1 \<Rightarrow> [ob\<^sub>1, r\<^sub>1]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
    ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> \<Prod>b \<leftarrow> [r\<^sub>1]. \<currency>\<^sup>?b \<parallel> ib\<^sub>1 \<Rightarrow> [ob\<^sub>1, r\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1"
    using sidetrack_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel>
    ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> \<Prod>b \<leftarrow> [r\<^sub>2]. \<currency>\<^sup>?b \<parallel> ib\<^sub>2 \<Rightarrow> [ob\<^sub>2, r\<^sub>2]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> \<currency>\<^sup>?r\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel>
    ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> \<Prod>b \<leftarrow> [r\<^sub>2]. \<currency>\<^sup>?b \<parallel> ib\<^sub>2 \<Rightarrow> [ob\<^sub>2, r\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2"
    using sidetrack_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel>
    ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> \<Prod>b \<leftarrow> [r\<^sub>3]. \<currency>\<^sup>?b \<parallel> ib\<^sub>3 \<Rightarrow> [ob\<^sub>3, r\<^sub>3]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel>
    ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> \<Prod>b \<leftarrow> [r\<^sub>3]. \<currency>\<^sup>?b \<parallel> ib\<^sub>3 \<Rightarrow> [ob\<^sub>3, r\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3"
    using sidetrack_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
    ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  finally show ?thesis .
qed

(* FIXME: Move this lemma to a common place for reuse by `Relaying_Broadcasting_Equivalence`. *)
lemma two_target_distributor_split:
  shows "\<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> a \<Rightarrow> [b\<^sub>1, b\<^sub>2] \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<currency>\<^sup>?b\<^sub>1 \<parallel> \<currency>\<^sup>?b\<^sub>2 \<parallel> a \<rightarrow> b\<^sub>1 \<parallel> a \<rightarrow> b\<^sub>2"
  sorry

lemma square_unidirectional_bridge_shortcut_redundancy:
  shows "a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> c \<rightarrow> d \<parallel> a \<rightarrow> d \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> c \<rightarrow> d"
proof -
  have "a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> c \<rightarrow> d \<parallel> a \<rightarrow> d \<approx>\<^sub>\<flat> c \<rightarrow> d \<parallel> a \<rightarrow> d \<parallel> a \<rightarrow> b \<parallel> b \<rightarrow> c"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> c \<rightarrow> d \<parallel> a \<rightarrow> d \<parallel> a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c \<parallel> c \<rightarrow> d \<parallel> a \<rightarrow> d"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c \<parallel> c \<rightarrow> d"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> c \<rightarrow> d \<parallel> a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> c \<rightarrow> d \<parallel> a \<rightarrow> b \<parallel> b \<rightarrow> c"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> c \<rightarrow> d"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma diamond_relaying_addition:
  shows "
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0" (is "?lhs \<approx>\<^sub>\<flat> ?rhs")
proof -
  \<comment> \<open>Node 0\<close>
  have "
    ?lhs
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    \<comment> \<open>node 0\<close> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    \<comment> \<open>node 0\<close> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"
    using distributor_shortcut_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"
    using two_target_distributor_split by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  \<comment> \<open>Node 1\<close>
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3"
    using square_unidirectional_bridge_shortcut_redundancy by equivalence
  \<comment> \<open>Node 2\<close>
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3"
    using square_unidirectional_bridge_shortcut_redundancy by equivalence
  \<comment> \<open>Node 3\<close>
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using square_unidirectional_bridge_shortcut_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>node 0\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>node 1\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>node 2\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>node 3\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using square_unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?rhs"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  finally show ?thesis .
qed

(* FIXME: Move this lemma to a common place for reuse by `Relaying_Broadcasting_Equivalence`. *)
lemma diamond_closure:
  shows "
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3"
  sorry

(* FIXME: Move this lemma to a common place for reuse by `Relaying_Broadcasting_Equivalence`. *)
lemma receive_collapse:
  shows "
    l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> a\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> a\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> a\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> a\<^sub>3
    \<approx>\<^sub>\<flat>
    l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> a\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> a\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> a\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"
  sorry

(* FIXME: Move this lemma to a common place for reuse by `Relaying_Broadcasting_Equivalence`. *)
lemma send_collapse:
  shows "
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> a\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> a\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    a\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> a\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]
    \<approx>\<^sub>\<flat>
    l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> a\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> a\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    a\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> a\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0"
  sorry

(* FIXME: Move this lemma to a common place for reuse by `Relaying_Broadcasting_Equivalence`. *)
lemma links_disconnect:
  shows "
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    \<approx>\<^sub>\<sharp>
    l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"
  sorry

(* FIXME: Move this lemma to a common place for reuse by `Relaying_Broadcasting_Equivalence`. *)
lemma links_remove:
  shows "
    \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1) \<parallel>
    \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2) \<parallel>
    \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
    \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3)
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0"
  sorry

lemma buffers_removal:
  shows "
    \<nu> ib ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<rightarrow> ob)
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r"
proof -
  have "
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob.  (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<rightarrow> ob)
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib)"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> ib)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ob \<rightarrow> m \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ib \<rightarrow> ob)"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ob \<rightarrow> m \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ib \<rightarrow> ob \<parallel> m \<rightarrow> ob)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> m \<rightarrow> ib \<parallel> m \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> ib \<rightarrow> ob \<parallel> ob \<rightarrow> m)"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> m \<rightarrow> ib \<parallel> m \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> ib \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel>
      ib \<rightarrow> m)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ob \<leftrightarrow> m \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>+m)"
    unfolding bidirectional_bridge_def and duploss_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ob \<leftrightarrow> m \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>+ib)"
    unfolding tagged_new_channel_def
    using
      duplication_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>+ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>?m)"
    unfolding duploss_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>+ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob)"
    unfolding tagged_new_channel_def
    using
      loss_channel_switch
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<Prod>b \<leftarrow> [r, ob]. \<currency>\<^sup>?b \<parallel> ib \<Rightarrow> [r, ob])"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<Prod>b \<leftarrow> [r, ob]. \<currency>\<^sup>?b \<parallel>
      \<Prod>b \<leftarrow> [r, ob]. ib \<rightarrow> b)"
    using distributor_split by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> m \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib \<rightarrow> r \<parallel>
      ib \<rightarrow> m \<parallel> m \<rightarrow> ob \<parallel> ib \<rightarrow> ob)"
    unfolding bidirectional_bridge_def and general_parallel.simps using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> m \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib \<rightarrow> r \<parallel> ib \<rightarrow> m \<parallel> m \<rightarrow> ob)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib \<rightarrow> r \<parallel> ib \<rightarrow> m \<parallel> m \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> ib)"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib \<rightarrow> r \<parallel> ib \<rightarrow> m \<parallel> m \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> ib \<rightarrow> r \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>*m)"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> ib \<rightarrow> r \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>*ib)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> ib \<rightarrow> r \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>*m)"
    unfolding duploss_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> ib \<rightarrow> r \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob \<parallel> ib \<leftrightarrow> m \<parallel> ib \<rightarrow> r)"
    unfolding duploss_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob \<parallel> ib \<leftrightarrow> m \<parallel> m \<rightarrow> r)"
    unfolding tagged_new_channel_def
    using
      unidirectional_bridge_source_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> \<currency>\<^sup>*ob \<parallel> ib \<leftrightarrow> m \<parallel> m \<rightarrow> r \<parallel> ob \<leftrightarrow> m \<parallel> s \<rightarrow> ob)"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> \<currency>\<^sup>*ob \<parallel> ib \<leftrightarrow> m \<parallel> m \<rightarrow> r \<parallel> ob \<leftrightarrow> m \<parallel> s \<rightarrow> m)"
    unfolding tagged_new_channel_def
    using
      unidirectional_bridge_target_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> \<langle>0\<rangle> \<nu> ib. (\<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ib) \<parallel> \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*ob \<parallel> m \<leftrightarrow> ob)"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> \<currency>\<^sup>*m \<parallel> \<currency>\<^sup>*m"
    unfolding tagged_new_channel_def using duploss_detour_collapse by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r"
    using natural_simps by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
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
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0]) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1]) \<parallel>
      \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2]) \<parallel>
      \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3])
    )"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0) \<parallel>
      (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1) \<parallel>
      (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2) \<parallel>
      (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3) \<parallel>
      \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
      ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3]
    ))"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0) \<parallel>
      (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1) \<parallel>
      (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2) \<parallel>
      (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3) \<parallel>
      \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
      ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel>
      ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3
    ))"
    using diamond_sidetrack_addition by equivalence
  (* FIXME: The following two steps are not strictly necessary, they're there so we can use
     `sidetrack_addition_diamond` as an aid to the reader. Discuss if this is really useful. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> sidetrack_addition_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel>
        \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
        l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
        l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
        l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
        l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3
      )
    )"
    unfolding duploss_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>?l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel>
        \<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>?l\<^sub>0\<^sub>2 \<parallel>
        l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
        l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
        l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
        l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
        l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
      )
    )"
    using diamond_relaying_addition by equivalence
  (* FIXME: The following two steps are not strictly necessary, they're there so we can use
     `buffered_relaying_diamond` as an aid to the reader. Discuss if this is really useful. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    unfolding duploss_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> buffered_relaying_diamond r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0
    )"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
      l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
      l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3
    )"
    using diamond_closure by equivalence
  (* FIXME: The following two steps are not strictly necessary, they're there so we can use
     `strongly_connected_network` as an aid to the reader. Discuss if this is really useful. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> strongly_connected_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel>
        s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel>
        s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel>
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel>
        l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
        l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
        l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3
      )
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel>
        s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel>
        s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel>
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel>
        l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
        l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3
      )
    )"
    using receive_collapse by equivalence
  (* FIXME: The following two steps are not strictly necessary, they're there so we can use
     `receive_collapsed_network` as an aid to the reader. Discuss if this is really useful. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> receive_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel>
        s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel>
        s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel>
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel>
        l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
        l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel> l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel>
        l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]
      )
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (
        s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel>
        s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel>
        s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel>
        s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel>
        l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
        l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>3\<^sub>0 \<parallel>
        ob\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0
      )
    )"
    using send_collapse by equivalence
  (* FIXME: The following two steps are not strictly necessary, they're there so we can use
     `send_collapsed_network` as an aid to the reader. Discuss if this is really useful. *)
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>0. \<langle>6\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>1. \<langle>8\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>9\<rangle> \<nu> ib\<^sub>2. \<langle>10\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>11\<rangle> \<nu> ib\<^sub>3. \<langle>12\<rangle> \<nu> ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>1 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel>
      l\<^sub>0\<^sub>2 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> send_collapsed_network r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
      l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3
    )"
    unfolding tagged_new_channel_def using links_disconnect by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1) \<parallel>
      \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2) \<parallel>
      \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
      \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3) \<parallel>
      \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
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
      \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"
    using natural_simps unfolding tagged_new_channel_def by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      \<nu> ib\<^sub>0 ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<nu> ib\<^sub>1 ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<nu> ib\<^sub>2 ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<nu> ib\<^sub>3 ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"
    using links_remove by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> buffered_broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      \<langle>1\<rangle> \<nu> ib\<^sub>0. \<langle>2\<rangle> \<nu> ob\<^sub>0. (s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>3\<rangle> \<nu> ib\<^sub>1. \<langle>4\<rangle> \<nu> ob\<^sub>1. (s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>2. \<langle>6\<rangle> \<nu> ob\<^sub>2. (s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      (\<langle>7\<rangle> \<nu> ib\<^sub>3. \<langle>8\<rangle> \<nu> ob\<^sub>3. (s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3))
    )"
    unfolding tagged_new_channel_def ..
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      \<langle>1\<rangle> \<nu> ib\<^sub>0. \<langle>2\<rangle> \<nu> ob\<^sub>0. (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>3\<rangle> \<nu> ib\<^sub>1. \<langle>4\<rangle> \<nu> ob\<^sub>1. (
        \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>5\<rangle> \<nu> ib\<^sub>2. \<langle>6\<rangle> \<nu> ob\<^sub>2. (
        \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>7\<rangle> \<nu> ib\<^sub>3. \<langle>8\<rangle> \<nu> ob\<^sub>3. (
        \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      \<nu> ib\<^sub>0 ob\<^sub>0. (\<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<nu> ib\<^sub>1 ob\<^sub>1. (\<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<nu> ib\<^sub>2 ob\<^sub>2. (\<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<nu> ib\<^sub>3 ob\<^sub>3. (\<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"
    using natural_simps unfolding tagged_new_channel_def by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      (\<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>0) \<parallel>
      (\<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>1) \<parallel>
      (\<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>2) \<parallel>
      (\<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>3)
    )"
    using buffers_removal by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> broadcast r\<^sub>0 s\<^sub>0 r\<^sub>1 s\<^sub>1 r\<^sub>2 s\<^sub>2 r\<^sub>3 s\<^sub>3"
    using natural_simps unfolding tagged_new_channel_def by equivalence
  finally show ?thesis .
qed

end
