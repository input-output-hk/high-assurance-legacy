section \<open>Equivalence of a Diamond-Shaped Relaying Network and a Cross-Shaped Broadcasting Network\<close>

theory Relaying_Broadcasting_Equivalence
  imports Chi_Calculus.Communication
begin

type_synonym four_node_network = "
  \<comment> \<open>Send interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Receive interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_send_interfacing = "
  \<comment> \<open>Send interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Links:\<close> [chan, chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_receive_interfacing = "
  \<comment> \<open>Receive interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Links:\<close> [chan, chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_core = "
  \<comment> \<open>Links:\<close> [chan, chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym cross_send_interfacing = "
  \<comment> \<open>Send interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Broadcast medium:\<close> chan \<Rightarrow>
  process"

type_synonym cross_receive_interfacing = "
  \<comment> \<open>Receive interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Broadcast medium:\<close> chan \<Rightarrow>
  process"

abbreviation diamond_send_interfacing :: diamond_send_interfacing where
  "diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"

abbreviation diamond_receive_interfacing :: diamond_receive_interfacing where
  "diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>0\<^sub>1 \<Rightarrow> [r\<^sub>1, l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>0\<^sub>2 \<Rightarrow> [r\<^sub>2, l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>1\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>2\<^sub>3 \<Rightarrow> [r\<^sub>3, l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<Rightarrow> [r\<^sub>0, l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]"

abbreviation diamond :: four_node_network where
  "diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"

abbreviation untangled_receive_interfacing :: diamond_receive_interfacing where
  "untangled_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0"

abbreviation untangled_core :: diamond_core where
  "untangled_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>From link 0--1:\<close> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>From link 0--2:\<close> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    \<comment> \<open>From link 1--3:\<close> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>From link 2--3:\<close> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>From link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"

abbreviation transformed_core :: diamond_core where
  "transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"

abbreviation cross_receive_interfacing :: cross_receive_interfacing where
  "cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> m \<rightarrow> r\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> m \<rightarrow> r\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> m \<rightarrow> r\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> m \<rightarrow> r\<^sub>3"

abbreviation cross_send_interfacing :: cross_send_interfacing where
  "cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<rightarrow> m"

abbreviation cross where
  "cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<parallel>
      cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m
    )"

lemma untangling:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    untangled_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    untangled_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
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

lemma core_transformation:
  shows "untangled_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<approx>\<^sub>\<flat> transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
proof -
  have "untangled_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close>
    (l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    \<comment> \<open>Right triangle:\<close>
    (l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close>
    (l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    \<comment> \<open>Right triangle:\<close>
    (l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close>
    (l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Right triangle:\<close>
    (l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close>
    (l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Right triangle:\<close>
    (l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  finally show ?thesis .
qed

lemma receive_interfacing_collapse:
  shows "
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    untangled_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0"
    using unidirectional_bridge_source_switch by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma send_interfacing_collapse:
  shows "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>0 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>1 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>2 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>0 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>1 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]. fst x \<leftrightarrow> snd x \<parallel> s\<^sub>2 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    by (intro
      basic_weak_parallel_preservation
      basic.weak.bisimilarity_reflexivity_rule
      distributor_target_switch [THEN basic.weak.bisimilarity_symmetry_rule]
    )
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core  l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>3\<^sub>0, l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core  l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (l\<^sub>3\<^sub>0 \<triangleleft> x \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core  l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using inner_duploss_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core  l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using send_idempotency_under_duploss by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core  l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x. l\<^sub>3\<^sub>0 \<triangleleft> x) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using inner_duploss_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core  l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding unidirectional_bridge_def by equivalence
  finally show ?thesis .
qed

lemma core_collapse:
  shows "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0"
proof -
  have "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Link 0--1:\<close> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3)"
    using natural_simps by equivalence
  also have"\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    unfolding tagged_new_channel_def using duploss_detour_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    using natural_simps by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
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
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        untangled_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        untangled_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using untangling by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      untangled_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      untangled_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      untangled_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using core_transformation by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        untangled_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using receive_interfacing_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using send_interfacing_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
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
      cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      \<currency>\<^sup>*l\<^sub>3\<^sub>0
    )"
    unfolding tagged_new_channel_def using core_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>4\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
qed

end
