theory Network_Equivalences
  imports Chi_Calculus.Communication
begin

abbreviation diamond_sending where
  "diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"

abbreviation diamond_receiving where
  "diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>0\<^sub>1 \<rightarrow> r\<^sub>1 \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>0\<^sub>2 \<rightarrow> r\<^sub>2 \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>1\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>2\<^sub>3 \<rightarrow> r\<^sub>3 \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> r\<^sub>0"

abbreviation initial_core where
  "initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>From link 0--1:\<close> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>From link 0--2:\<close> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    \<comment> \<open>From link 1--3:\<close> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>From link 2--3:\<close> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>From link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2"

abbreviation transformed_core where
  "transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3"

abbreviation cross_sending where
  "cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<rightarrow> m"

abbreviation cross_receiving where
  "cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> m \<rightarrow> r\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> m \<rightarrow> r\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> m \<rightarrow> r\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> m \<rightarrow> r\<^sub>3"

lemma focussing:
  shows "a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> c \<rightarrow> a \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> a \<leftrightarrow> c" (is "?p \<approx>\<^sub>\<flat> ?q")
proof-
  have "?p \<approx>\<^sub>\<flat>
    (a \<rightarrow> b \<parallel> b \<rightarrow> c) \<parallel>
    (b \<rightarrow> c \<parallel> c \<rightarrow> a)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    (a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c) \<parallel>
    (b \<rightarrow> c \<parallel> c \<rightarrow> a \<parallel> b \<rightarrow> a)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    a \<rightarrow> b \<parallel> c \<rightarrow> a \<parallel>
    (b \<rightarrow> a \<parallel> a \<rightarrow> c \<parallel> b \<rightarrow> c)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    a \<rightarrow> b \<parallel> c \<rightarrow> a \<parallel>
    (b \<rightarrow> a \<parallel> a \<rightarrow> c)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  finally show ?thesis .
qed

lemma core_transformation:
  shows "initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<approx>\<^sub>\<flat> transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
proof -
  have "initial_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    \<comment> \<open>Right triangle:\<close> (l\<^sub>3\<^sub>0 \<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>1\<^sub>3) \<parallel>
    \<comment> \<open>Right triangle:\<close> (l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 \<leftrightarrow> l\<^sub>2\<^sub>3)"
    using focussing by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  finally show ?thesis .
qed

lemma sending_collapse:
  shows "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    cross_sending s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 l\<^sub>3\<^sub>0"
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
      distributor_target_switch [THEN basic.weak.bisimilarity_symmetry_rule]
      basic.weak.bisimilarity_reflexivity_rule
      basic_weak_parallel_preservation
    )
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>3\<^sub>0, l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (l\<^sub>3\<^sub>0 \<triangleleft> x \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using inner_duploss_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using send_idempotency_under_duploss by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> s\<^sub>0 \<triangleright>\<^sup>\<infinity> x. l\<^sub>3\<^sub>0 \<triangleleft> x) \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using inner_duploss_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding unidirectional_bridge_def by equivalence
  finally show ?thesis .
qed

lemma receiving_collapse:
  shows "
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    transformed_core l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    cross_receiving r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 l\<^sub>3\<^sub>0"
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

end
