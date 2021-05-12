theory "Thorn_Calculus-Experiments"
imports
  "Thorn_Calculus-Semantics-Synchronous"
begin

lemma
  shows "\<not> \<nu> a. \<nu> b. \<box> a \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> P" (is "\<not> ?v")
proof
  assume ?v
  then show False
  proof cases
    case opening
    from opening(4) show False
    proof cases
      case opening
      from opening(4) show False
        by cases
    next
      case new_channel_io
      from new_channel_io(2) show False
        by cases
    qed
  next
    case new_channel_io
    from new_channel_io(3) show False
    proof cases
      case opening
      from opening(5) show False
        by cases
    next
      case new_channel_io
      from new_channel_io(2) show False
        by cases
    qed
  next
    case new_channel_communication
    from new_channel_communication(3) show False
    proof cases
      case new_channel_communication
      from new_channel_communication(2) show False
        by cases
    qed
  qed
qed

lemma
  shows "\<not> \<nu> a. \<nu> b. \<nu> c. \<box> a \<triangleleft> X \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> P" (is "\<not> ?v")
proof
  assume ?v
  then show False
  proof cases
    case opening
    from opening(4) show False
    proof cases
      case opening
      from opening(4) show False
      proof cases
        case opening
        from opening(4) show False
          by cases
      next
        case new_channel_io
        from new_channel_io(2) show False
          by cases
      qed
    next
      case new_channel_io
      from new_channel_io(2) show False
      proof cases
        case opening
        from opening(4) show False
          by cases
      next
        case new_channel_io
        from new_channel_io(2) show False
          by cases
      qed
    qed
  next
    case new_channel_io
    from new_channel_io(3) show False
    proof cases
      case opening
      from opening(5) show False
      proof cases
        case opening
        from opening(4) show False
          by cases
      next
        case new_channel_io
        from new_channel_io(2) show False
          by cases
      qed
    next
      case new_channel_io
      from new_channel_io(2) show False
      proof cases
        case opening
        from opening(5) show False
          by cases
      next
        case new_channel_io
        from new_channel_io(2) show False
          by cases
      qed
    qed
  next
    case new_channel_communication
    from new_channel_communication(3) show False
    proof cases
      case new_channel_communication
      from new_channel_communication(2) show False
      proof cases
        case new_channel_communication
        from new_channel_communication(2) show False
          by cases
      qed
    qed
  qed
qed

lemma
  shows "\<not> \<nu> c. ((c \<noteq> a) ? \<box> c \<triangleleft> X \<parallel> \<box> c \<triangleright> x. B \<triangleleft> \<box> x) \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> P" (is "\<not> ?v")
proof
  assume ?v
  then show False
  proof cases
    case opening
    from opening(4) show False
    proof cases
      case parallel_left_io
      from parallel_left_io(2) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case parallel_right_io
      from parallel_right_io(2) show False
        by cases
    qed
  next
    case new_channel_io
    from new_channel_io(3) show False
    proof cases
      case parallel_left_io
      from parallel_left_io(2) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case parallel_right_io
      from parallel_right_io(2) show False
        by cases
    qed
  next
    case new_channel_communication
    from new_channel_communication(3) show False
    proof cases
      case communication
      from communication(3) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case parallel_left_communication
      from parallel_left_communication(2) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case parallel_right_communication
      from parallel_right_communication(2) show False
        by cases
    qed
  qed
qed

lemma other_channel_exists:
  fixes a :: chan
  obtains b where "b \<noteq> a"
proof -
  obtain c ::chan and d :: chan where "c \<noteq> d"
    using more_than_one_chan
    by blast
  show thesis
  proof (cases "a = c")
    case True
    with \<open>c \<noteq> d\<close> have "d \<noteq> a"
      by simp
    with that show ?thesis
      by simp
  next
    case False
    with that show ?thesis
      by fast
  qed
qed

lemma
  shows "\<not> \<nu> c. ((c = a) ? B \<triangleleft> X \<parallel> (c \<noteq> a) ? B \<triangleleft> X) \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> P" (is "\<not> ?v")
proof
  obtain d :: chan where "d \<noteq> a"
    using other_channel_exists .
  assume ?v
  moreover have "\<not> \<nabla> (\<lambda>c. (c = a) ? B \<triangleleft> X) \<parallel> \<nabla> (\<lambda>c. (c \<noteq> a) ? B \<triangleleft> X) \<rightarrow>\<^sub>s\<lparr>\<beta>\<rparr> Q" for \<beta> and Q
  proof
    assume "\<nabla> (\<lambda>c. (c = a) ? B \<triangleleft> X) \<parallel> \<nabla> (\<lambda>c. (c \<noteq> a) ? B \<triangleleft> X) \<rightarrow>\<^sub>s\<lparr>\<beta>\<rparr> Q"
    then show False
    proof cases
      case communication
      from communication(4) and \<open>d \<noteq> a\<close>  show False
        by cases (auto dest: fun_cong [where x = "d ## undefined"])
    next
      case parallel_left_io
      from parallel_left_io(3) and \<open>d \<noteq> a\<close> show False
        by cases (auto dest: fun_cong [where x = "d ## undefined"])
    next
      case parallel_right_io
      from parallel_right_io(3) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case parallel_left_communication
      from parallel_left_communication(3) and \<open>d \<noteq> a\<close> show False
        by cases (auto dest: fun_cong [where x = "d ## undefined"])
    next
      case parallel_right_communication
      from parallel_right_communication(3) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    qed
  qed
  ultimately show False
    by cases simp_all
qed

end
