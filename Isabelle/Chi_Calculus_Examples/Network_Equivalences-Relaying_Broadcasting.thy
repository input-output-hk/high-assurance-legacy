section \<open>Equivalence of a Diamond-Shaped Relaying Network and a Cross-Shaped Broadcasting Network\<close>

theory "Network_Equivalences-Relaying_Broadcasting"
  imports Network_Equivalences
begin

abbreviation diamond_receiving_and_relaying where
  "diamond_receiving_and_relaying r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"

abbreviation diamond  where
  "diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving_and_relaying r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"

abbreviation cross where
  "cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m
    )"

lemma untangling:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving_and_relaying r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<comment> \<open>Link 0--1:\<close> (\<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>1, l\<^sub>1\<^sub>3]. \<currency>\<^sup>?a \<parallel> l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3]) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (\<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>2, l\<^sub>2\<^sub>3]. \<currency>\<^sup>?a \<parallel> l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3]) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (\<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>3, l\<^sub>3\<^sub>0]. \<currency>\<^sup>?a \<parallel> l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0]) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (\<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>3, l\<^sub>3\<^sub>0]. \<currency>\<^sup>?a \<parallel> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0]) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?a \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2])"
    unfolding duploss_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Link 0--1:\<close> (\<currency>\<^sup>+l\<^sub>0\<^sub>1 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>1, l\<^sub>1\<^sub>3]. \<currency>\<^sup>?a \<parallel> \<Prod>a\<leftarrow>[r\<^sub>1, l\<^sub>1\<^sub>3]. l\<^sub>0\<^sub>1 \<rightarrow> a) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (\<currency>\<^sup>+l\<^sub>0\<^sub>2 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>2, l\<^sub>2\<^sub>3]. \<currency>\<^sup>?a \<parallel> \<Prod>a\<leftarrow>[r\<^sub>2, l\<^sub>2\<^sub>3]. l\<^sub>0\<^sub>2 \<rightarrow> a) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (\<currency>\<^sup>+l\<^sub>1\<^sub>3 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>3, l\<^sub>3\<^sub>0]. \<currency>\<^sup>?a \<parallel> \<Prod>a\<leftarrow>[r\<^sub>3, l\<^sub>3\<^sub>0]. l\<^sub>1\<^sub>3 \<rightarrow> a) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (\<currency>\<^sup>+l\<^sub>2\<^sub>3 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>3, l\<^sub>3\<^sub>0]. \<currency>\<^sup>?a \<parallel> \<Prod>a\<leftarrow>[r\<^sub>3, l\<^sub>3\<^sub>0]. l\<^sub>2\<^sub>3 \<rightarrow> a) \<parallel>
    \<comment> \<open>Link 3--0:\<close> (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Prod>a\<leftarrow>[r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?a \<parallel> \<Prod>a\<leftarrow>[r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. l\<^sub>3\<^sub>0 \<rightarrow> a)"
    using distributor_split by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding duploss_def and general_parallel.simps using natural_simps by equivalence
  finally show ?thesis .
qed

theorem diamond_cross_equivalence:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3"
proof -
  have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving_and_relaying r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving_and_relaying r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using untangling by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using core_transformation by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using receiving_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using sending_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (
          \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
          transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
        )
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      \<currency>\<^sup>*l\<^sub>3\<^sub>0
    )"
    unfolding tagged_new_channel_def using core_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
qed

end
