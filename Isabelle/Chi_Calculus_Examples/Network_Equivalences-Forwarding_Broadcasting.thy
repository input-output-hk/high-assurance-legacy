section \<open>Equivalence of a Diamond-Shaped Forwarding Network and a Cross-Shaped Broadcasting Network\<close>

theory "Network_Equivalences-Forwarding_Broadcasting"
  imports Network_Equivalences
begin

type_synonym diamond_send_transfer = "
  \<comment> \<open>Send interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Send buffers:\<close> [chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_receive_transfer_and_forwarding = "
  \<comment> \<open>Receive interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Send buffers:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Receive buffers:\<close> [chan, chan, chan, chan] \<Rightarrow>
  process"

abbreviation diamond_send_transfer :: diamond_send_transfer where
  "diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<rightarrow> sb\<^sub>3"

abbreviation diamond_receive_transfer_and_forwarding :: diamond_receive_transfer_and_forwarding where
  "diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel>
    \<comment> \<open>Node 2:\<close> rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel>
    \<comment> \<open>Node 3:\<close> rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3]"

abbreviation diamond :: four_node_network where
  "diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"

abbreviation buffer_sidetracks where
  "buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> rb\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> rb\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> rb\<^sub>3 \<rightarrow> sb\<^sub>3"

abbreviation cross where
  "cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<parallel>
      cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m
    )"

lemma buffer_sidetrack_addition:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<comment> \<open>Node 0:\<close> (\<Prod>b\<leftarrow>[r\<^sub>0]. \<currency>\<^sup>?b \<parallel> rb\<^sub>0 \<Rightarrow> [sb\<^sub>0, r\<^sub>0]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>b\<leftarrow>[r\<^sub>1]. \<currency>\<^sup>?b \<parallel> rb\<^sub>1 \<Rightarrow> [sb\<^sub>1, r\<^sub>1]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>b\<leftarrow>[r\<^sub>2]. \<currency>\<^sup>?b \<parallel> rb\<^sub>2 \<Rightarrow> [sb\<^sub>2, r\<^sub>2]) \<parallel>
    \<comment> \<open>Node 3:\<close> (\<Prod>b\<leftarrow>[r\<^sub>3]. \<currency>\<^sup>?b \<parallel> rb\<^sub>3 \<Rightarrow> [sb\<^sub>3, r\<^sub>3])"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Node 0:\<close> (\<Prod>b\<leftarrow>[r\<^sub>0]. \<currency>\<^sup>?b \<parallel> rb\<^sub>0 \<Rightarrow> [sb\<^sub>0, r\<^sub>0] \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>b\<leftarrow>[r\<^sub>1]. \<currency>\<^sup>?b \<parallel> rb\<^sub>1 \<Rightarrow> [sb\<^sub>1, r\<^sub>1] \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>b\<leftarrow>[r\<^sub>2]. \<currency>\<^sup>?b \<parallel> rb\<^sub>2 \<Rightarrow> [sb\<^sub>2, r\<^sub>2] \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    \<comment> \<open>Node 3:\<close> (\<Prod>b\<leftarrow>[r\<^sub>3]. \<currency>\<^sup>?b \<parallel> rb\<^sub>3 \<Rightarrow> [sb\<^sub>3, r\<^sub>3] \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3)"
    using sidetrack_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  finally show ?thesis .
qed

(* TODO: Perhaps this is a coarse-grained step, overhaul it. *)
lemma core_relaying:
  shows "
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel> sb\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel> sb\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel> sb\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3] \<parallel> sb\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
    \<comment> \<open>Node 1:\<close> (l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    \<comment> \<open>Node 2:\<close> (l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    \<comment> \<open>Node 3:\<close> (l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel> sb\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel> sb\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel> sb\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3] \<parallel> sb\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> sb\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> sb\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>2\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel> sb\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3]"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> sb\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> sb\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>2\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel> sb\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3]"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> sb\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel>
    rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel> sb\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel> sb\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3] \<parallel> sb\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> sb\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3) \<parallel>
    rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel>
    rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel> sb\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel> sb\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3] \<parallel> sb\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0"
    using unidirectional_bridge_shortcut_redundancy and distributor_shortcut_redundancy
    by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?b \<parallel> l\<^sub>3\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    unfolding duploss_def and unidirectional_bridge_def and general_parallel.simps
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. l\<^sub>3\<^sub>0 \<rightarrow> b) \<parallel>
    (l\<^sub>3\<^sub>0 \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
    diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0"
    using distributor_split and unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding duploss_def and general_parallel.simps using natural_simps by equivalence
  finally show ?thesis .
qed

lemma node_buffering_removal:
  shows "
    \<nu> sb rb. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> sb \<rightarrow> m \<parallel> m \<rightarrow> rb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> rb \<rightarrow> sb)
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r"
proof -
  have "
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> sb \<rightarrow> m \<parallel> m \<rightarrow> rb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> rb \<rightarrow> sb)
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> rb \<rightarrow> sb \<parallel> sb \<rightarrow> m \<parallel> m \<rightarrow> rb)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> rb \<rightarrow> sb \<parallel> sb \<rightarrow> m \<parallel> m \<rightarrow> rb \<parallel> sb \<rightarrow> rb)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> sb \<rightarrow> m \<parallel> sb \<rightarrow> rb \<parallel> m \<rightarrow> rb \<parallel> rb \<rightarrow> sb)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> sb \<rightarrow> m \<parallel> sb \<rightarrow> rb \<parallel> m \<rightarrow> rb \<parallel> rb \<rightarrow> sb \<parallel> m \<rightarrow> sb)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> m \<rightarrow> rb \<parallel> m \<rightarrow> sb \<parallel> sb \<rightarrow> rb \<parallel> rb \<rightarrow> sb \<parallel> sb \<rightarrow> m)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> m \<rightarrow> rb \<parallel> m \<rightarrow> sb \<parallel> sb \<rightarrow> rb \<parallel> rb \<rightarrow> sb \<parallel> sb \<rightarrow> m \<parallel>
      rb \<rightarrow> m)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> sb \<leftrightarrow> m \<parallel> rb \<leftrightarrow> sb \<parallel> m \<leftrightarrow> rb \<parallel> \<currency>\<^sup>+m)"
    unfolding bidirectional_bridge_def and duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> sb \<leftrightarrow> m \<parallel> rb \<leftrightarrow> sb \<parallel> m \<leftrightarrow> rb \<parallel> \<currency>\<^sup>+rb)"
    unfolding tagged_new_channel_def
    using
      duplication_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> rb \<leftrightarrow> sb \<parallel> m \<leftrightarrow> rb \<parallel> \<currency>\<^sup>+rb \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>?m)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<Rightarrow> [r, sb] \<parallel> rb \<leftrightarrow> sb \<parallel> m \<leftrightarrow> rb \<parallel> \<currency>\<^sup>+rb \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>?sb)"
    unfolding tagged_new_channel_def
    using
      loss_channel_switch
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<leftrightarrow> sb \<parallel> m \<leftrightarrow> rb \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>+rb \<parallel> \<Prod>b \<leftarrow> [r, sb]. \<currency>\<^sup>?b \<parallel> rb \<Rightarrow> [r, sb])"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> rb \<leftrightarrow> sb \<parallel> m \<leftrightarrow> rb \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>+rb \<parallel> \<Prod>b \<leftarrow> [r, sb]. \<currency>\<^sup>?b \<parallel>
      \<Prod>b \<leftarrow> [r, sb]. rb \<rightarrow> b)"
    using distributor_split by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> sb \<rightarrow> rb \<parallel> m \<rightarrow> rb \<parallel> sb \<rightarrow> m \<parallel> \<currency>\<^sup>+rb \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?sb \<parallel> rb \<rightarrow> r \<parallel>
      rb \<rightarrow> m \<parallel> m \<rightarrow> sb \<parallel> rb \<rightarrow> sb)"
    unfolding bidirectional_bridge_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> sb \<rightarrow> rb \<parallel> m \<rightarrow> rb \<parallel> sb \<rightarrow> m \<parallel> \<currency>\<^sup>+rb \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?sb \<parallel> rb \<rightarrow> r \<parallel> rb \<rightarrow> m \<parallel> m \<rightarrow> sb)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> \<currency>\<^sup>+rb \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?sb \<parallel> rb \<rightarrow> r \<parallel> rb \<rightarrow> m \<parallel> m \<rightarrow> sb \<parallel> sb \<rightarrow> m \<parallel> m \<rightarrow> rb \<parallel> sb \<rightarrow> rb)"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> \<currency>\<^sup>+rb \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?sb \<parallel> rb \<rightarrow> r \<parallel> rb \<rightarrow> m \<parallel> m \<rightarrow> sb \<parallel> sb \<rightarrow> m \<parallel> m \<rightarrow> rb)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> \<currency>\<^sup>+rb \<parallel> \<currency>\<^sup>?r \<parallel> rb \<rightarrow> r \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>?sb \<parallel> m \<leftrightarrow> rb \<parallel> \<currency>\<^sup>*m)"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> \<currency>\<^sup>+rb \<parallel> \<currency>\<^sup>?r \<parallel> rb \<rightarrow> r \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>?sb \<parallel> m \<leftrightarrow> rb \<parallel> \<currency>\<^sup>*rb)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> \<currency>\<^sup>?r \<parallel> rb \<rightarrow> r \<parallel> \<currency>\<^sup>?sb \<parallel> m \<leftrightarrow> rb \<parallel> \<currency>\<^sup>*rb \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>*m)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> \<currency>\<^sup>?r \<parallel> rb \<rightarrow> r \<parallel> \<currency>\<^sup>?sb \<parallel> m \<leftrightarrow> rb \<parallel> \<currency>\<^sup>*rb \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>*sb)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*rb \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>*sb \<parallel> rb \<leftrightarrow> m \<parallel> rb \<rightarrow> r)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> sb \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*rb \<parallel> m \<leftrightarrow> sb \<parallel> \<currency>\<^sup>*sb \<parallel> rb \<leftrightarrow> m \<parallel> m \<rightarrow> r)"
    unfolding tagged_new_channel_def
    using
      unidirectional_bridge_source_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>*m \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*rb \<parallel> \<currency>\<^sup>*sb \<parallel> rb \<leftrightarrow> m \<parallel> m \<rightarrow> r \<parallel> sb \<leftrightarrow> m \<parallel> s \<rightarrow> sb)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb. \<langle>1\<rangle> \<nu> rb. (\<currency>\<^sup>*m \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*rb \<parallel> \<currency>\<^sup>*sb \<parallel> rb \<leftrightarrow> m \<parallel> m \<rightarrow> r \<parallel> sb \<leftrightarrow> m \<parallel> s \<rightarrow> m)"
    unfolding tagged_new_channel_def
    using
      unidirectional_bridge_target_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m \<rightarrow> r \<parallel> \<langle>0\<rangle> \<nu> rb. (\<currency>\<^sup>*rb \<parallel> m \<leftrightarrow> rb) \<parallel> \<langle>1\<rangle> \<nu> sb. (\<currency>\<^sup>*sb \<parallel> m \<leftrightarrow> sb)"
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
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
        buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3
      )
    )"
    using buffer_sidetrack_addition by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
        buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
        buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
        initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using core_relaying by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using core_transformation by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      (
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      (
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using receiving_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      cross_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      cross_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using sending_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      cross_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
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
    \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>4\<rangle> \<nu> rb\<^sub>0. \<langle>5\<rangle> \<nu> rb\<^sub>1. \<langle>6\<rangle> \<nu> rb\<^sub>2. \<langle>7\<rangle> \<nu> rb\<^sub>3.
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_transfer s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 \<parallel>
      diamond_receive_transfer_and_forwarding r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      buffer_sidetracks sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 \<parallel>
      cross_receiving rb\<^sub>0 rb\<^sub>1 rb\<^sub>2 rb\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_sending sb\<^sub>0 sb\<^sub>1 sb\<^sub>2 sb\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      \<currency>\<^sup>*l\<^sub>3\<^sub>0
    )"
    unfolding tagged_new_channel_def using core_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>12\<rangle> \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      \<langle>0\<rangle> \<nu> sb\<^sub>0. \<langle>4\<rangle> \<nu> rb\<^sub>0. (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>0 \<rightarrow> sb\<^sub>0 \<parallel> sb\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> rb\<^sub>0 \<parallel> rb\<^sub>0 \<Rightarrow> [r\<^sub>0, sb\<^sub>0] \<parallel> rb\<^sub>0 \<rightarrow> sb\<^sub>0) \<parallel>
      \<langle>1\<rangle> \<nu> sb\<^sub>1. \<langle>5\<rangle> \<nu> rb\<^sub>1. (
        \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>1 \<rightarrow> sb\<^sub>1 \<parallel> sb\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> rb\<^sub>1 \<parallel> rb\<^sub>1 \<Rightarrow> [r\<^sub>1, sb\<^sub>1] \<parallel> rb\<^sub>1 \<rightarrow> sb\<^sub>1) \<parallel>
      \<langle>2\<rangle> \<nu> sb\<^sub>2. \<langle>6\<rangle> \<nu> rb\<^sub>2. (
        \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>2 \<rightarrow> sb\<^sub>2 \<parallel> sb\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> rb\<^sub>2 \<parallel> rb\<^sub>2 \<Rightarrow> [r\<^sub>2, sb\<^sub>2] \<parallel> rb\<^sub>2 \<rightarrow> sb\<^sub>2) \<parallel>
      \<langle>3\<rangle> \<nu> sb\<^sub>3. \<langle>7\<rangle> \<nu> rb\<^sub>3. (
        \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>3 \<rightarrow> sb\<^sub>3 \<parallel> sb\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> rb\<^sub>3 \<parallel> rb\<^sub>3 \<Rightarrow> [r\<^sub>3, sb\<^sub>3] \<parallel> rb\<^sub>3 \<rightarrow> sb\<^sub>3)
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

