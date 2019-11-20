section \<open>Equivalence of a Diamond-Shaped Forwarding Network and a Cross-Shaped Broadcasting Network\<close>

theory "Network_Equivalences-Forwarding_Broadcasting"
  imports Network_Equivalences
begin

type_synonym diamond_send_interfacing = "
  \<comment> \<open>Send interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Send buffer:\<close> [chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_receive_interfacing = "
  \<comment> \<open>Receive interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Receive buffering:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Send buffering:\<close> [chan, chan, chan, chan] \<Rightarrow>
  process"

abbreviation diamond_send_interfacing :: diamond_send_interfacing where
  "diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<rightarrow> ob\<^sub>3"

abbreviation diamond_receive_interfacing :: diamond_receive_interfacing where
  "diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel>
    \<comment> \<open>Node 2:\<close> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
    \<comment> \<open>Node 3:\<close> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3]"

abbreviation diamond :: four_node_network where
  "diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"

abbreviation receive_send_sidetrack where
  "receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> ib\<^sub>3 \<rightarrow> ob\<^sub>3"

abbreviation cross where
  "cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m
    )"

lemma receive_send_sidetracking:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<comment> \<open>Node 0:\<close> (\<Prod>b\<leftarrow>[r\<^sub>0]. \<currency>\<^sup>?b \<parallel> ib\<^sub>0 \<Rightarrow> [ob\<^sub>0, r\<^sub>0]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>b\<leftarrow>[r\<^sub>1]. \<currency>\<^sup>?b \<parallel> ib\<^sub>1 \<Rightarrow> [ob\<^sub>1, r\<^sub>1]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>b\<leftarrow>[r\<^sub>2]. \<currency>\<^sup>?b \<parallel> ib\<^sub>2 \<Rightarrow> [ob\<^sub>2, r\<^sub>2]) \<parallel>
    \<comment> \<open>Node 3:\<close> (\<Prod>b\<leftarrow>[r\<^sub>3]. \<currency>\<^sup>?b \<parallel> ib\<^sub>3 \<Rightarrow> [ob\<^sub>3, r\<^sub>3])"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Node 0:\<close> (\<Prod>b\<leftarrow>[r\<^sub>0]. \<currency>\<^sup>?b \<parallel> ib\<^sub>0 \<Rightarrow> [ob\<^sub>0, r\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>b\<leftarrow>[r\<^sub>1]. \<currency>\<^sup>?b \<parallel> ib\<^sub>1 \<Rightarrow> [ob\<^sub>1, r\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>b\<leftarrow>[r\<^sub>2]. \<currency>\<^sup>?b \<parallel> ib\<^sub>2 \<Rightarrow> [ob\<^sub>2, r\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
    \<comment> \<open>Node 3:\<close> (\<Prod>b\<leftarrow>[r\<^sub>3]. \<currency>\<^sup>?b \<parallel> ib\<^sub>3 \<Rightarrow> [ob\<^sub>3, r\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)"
    using sidetrack_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  finally show ?thesis .
qed

(* TODO: Perhaps this is a coarse-grained step, overhaul it. *)
lemma core_relaying:
  shows "
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
    ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
    \<comment> \<open>Node 1:\<close> (l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
    \<comment> \<open>Node 2:\<close> (l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
    \<comment> \<open>Node 3:\<close> (l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
    ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>2\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3]"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>2\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3]"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
    ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
    ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3) \<parallel>
    ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
    ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0"
    using unidirectional_bridge_shortcut_redundancy and distributor_shortcut_redundancy
    by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?b \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
    diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    unfolding duploss_def and unidirectional_bridge_def and general_parallel.simps
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. l\<^sub>3\<^sub>0 \<rightarrow> b) \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
    diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using distributor_split and unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding duploss_def and general_parallel.simps using natural_simps by equivalence
  finally show ?thesis .
qed

lemma node_buffering_removal:
  shows "
    \<nu> ib ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<rightarrow> ob)
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r"
proof -
  have "
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<rightarrow> ob)
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> ib)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ob \<rightarrow> m \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ib \<rightarrow> ob)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ob \<rightarrow> m \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ib \<rightarrow> ob \<parallel> m \<rightarrow> ob)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> m \<rightarrow> ib \<parallel> m \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> ib \<rightarrow> ob \<parallel> ob \<rightarrow> m)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> m \<rightarrow> ib \<parallel> m \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> ib \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel>
      ib \<rightarrow> m)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ob \<leftrightarrow> m \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>+m)"
    unfolding bidirectional_bridge_def and duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ob \<leftrightarrow> m \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>+ib)"
    unfolding tagged_new_channel_def
    using
      duplication_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>+ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>?m)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<Rightarrow> [r, ob] \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>+ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob)"
    unfolding tagged_new_channel_def
    using
      loss_channel_switch
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<Prod>b \<leftarrow> [r, ob]. \<currency>\<^sup>?b \<parallel> ib \<Rightarrow> [r, ob])"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib \<leftrightarrow> ob \<parallel> m \<leftrightarrow> ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<Prod>b \<leftarrow> [r, ob]. \<currency>\<^sup>?b \<parallel>
      \<Prod>b \<leftarrow> [r, ob]. ib \<rightarrow> b)"
    using distributor_split by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> m \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib \<rightarrow> r \<parallel>
      ib \<rightarrow> m \<parallel> m \<rightarrow> ob \<parallel> ib \<rightarrow> ob)"
    unfolding bidirectional_bridge_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> m \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib \<rightarrow> r \<parallel> ib \<rightarrow> m \<parallel> m \<rightarrow> ob)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib \<rightarrow> r \<parallel> ib \<rightarrow> m \<parallel> m \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> ib)"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib \<rightarrow> r \<parallel> ib \<rightarrow> m \<parallel> m \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> ib \<rightarrow> r \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>*m)"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> ib \<rightarrow> r \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>*ib)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> ib \<rightarrow> r \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>*m)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> ib \<rightarrow> r \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow> ib \<parallel> \<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob \<parallel> ib \<leftrightarrow> m \<parallel> ib \<rightarrow> r)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob \<parallel> ib \<leftrightarrow> m \<parallel> m \<rightarrow> r)"
    unfolding tagged_new_channel_def
    using
      unidirectional_bridge_source_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> \<currency>\<^sup>*ob \<parallel> ib \<leftrightarrow> m \<parallel> m \<rightarrow> r \<parallel> ob \<leftrightarrow> m \<parallel> s \<rightarrow> ob)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> \<currency>\<^sup>*ob \<parallel> ib \<leftrightarrow> m \<parallel> m \<rightarrow> r \<parallel> ob \<leftrightarrow> m \<parallel> s \<rightarrow> m)"
    unfolding tagged_new_channel_def
    using
      unidirectional_bridge_target_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> \<langle>0\<rangle> \<nu> ib. (\<currency>\<^sup>*ib \<parallel> m \<leftrightarrow> ib) \<parallel> \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*ob \<parallel> m \<leftrightarrow> ob)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> \<currency>\<^sup>*m \<parallel> \<currency>\<^sup>*m"
    unfolding tagged_new_channel_def using duploss_detour_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r"
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
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
        receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
      )
    )"
    using receive_send_sidetracking by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
        receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
        receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
        initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using core_relaying by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using core_transformation by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      (
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      (
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using receiving_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      cross_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      cross_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using sending_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      cross_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. (
          \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
          transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
        )
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      cross_receiving ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_sending ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      \<currency>\<^sup>*l\<^sub>3\<^sub>0
    )"
    unfolding tagged_new_channel_def using core_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>12\<rangle> \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>4\<rangle> \<nu> ob\<^sub>0. (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 \<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 \<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>5\<rangle> \<nu> ob\<^sub>1. (
        \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 \<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 \<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>6\<rangle> \<nu> ob\<^sub>2. (
        \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 \<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 \<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>7\<rangle> \<nu> ob\<^sub>3. (
        \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 \<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 \<rightarrow> ob\<^sub>3)
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>12\<rangle> \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      (\<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>0) \<parallel>
      (\<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>1) \<parallel>
      (\<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>2) \<parallel>
      (\<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> r\<^sub>3)
    )"
    unfolding tagged_new_channel_def using node_buffering_removal by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3"
    using natural_simps unfolding tagged_new_channel_def by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
qed

end

