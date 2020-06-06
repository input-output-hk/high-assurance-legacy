theory "Thorn_Calculus-Experiments"
imports
  "Thorn_Calculus-Transition_System"
begin

lemma
  shows "\<not> \<nu> a. \<nu> b. \<langle>a\<rangle> \<triangleleft> X \<rightarrow>\<lparr>\<alpha>\<rparr> P"
proof
  assume "\<nu> a. \<nu> b. \<langle>a\<rangle> \<triangleleft> X \<rightarrow>\<lparr>\<alpha>\<rparr> P"
  then show False
  proof cases
    case opening
    from opening(4) show False
    proof cases
      case opening
      from opening(4) show False
        by cases
    next
      case new_channel
      from new_channel(2) show False
        by cases simp
    qed
  next
    case new_channel
    from new_channel(2) show False
    proof cases
      case opening
      from opening(4) and opening(1) show False
        by cases auto
    next
      case new_channel
      from new_channel(2) show False
        by cases auto
    qed
  qed
qed

lemma
  shows "\<not> \<nu> a. \<nu> b. \<nu> c. \<langle>a\<rangle> \<triangleleft> X \<rightarrow>\<lparr>\<alpha>\<rparr> P"
proof
  assume "\<nu> a. \<nu> b. \<nu> c. \<langle>a\<rangle> \<triangleleft> X \<rightarrow>\<lparr>\<alpha>\<rparr> P"
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
        case new_channel
        from new_channel(2) show False
          by cases simp
      qed
    next
      case new_channel
      from new_channel(2) show False
      proof cases
        case opening
        from opening(4) and opening(1) show False
          by cases auto
      next
        case new_channel
        from new_channel(2) show False
          by cases simp
      qed
    qed
  next
    case new_channel
    from new_channel(2) show False
    proof cases
      case opening
      note new_channel_opening_1 = opening(1)
      from opening(4) show False
      proof cases
        case opening
        from opening(4) and new_channel_opening_1 show False
          by cases auto
      next
        case new_channel
        from new_channel(2) and new_channel_opening_1 show False
          by cases auto
      qed
    next
      case new_channel
      from new_channel(2) show False
      proof cases
        case opening
        from opening(4) and opening(1) show False
          by cases auto
      next
        case new_channel
        from new_channel(2) show False
          by cases auto
      qed
    qed
  qed
qed

lemma
  shows "\<not> \<nu> c. ((c \<noteq> a) ? \<langle>c\<rangle> \<triangleleft> X \<parallel> \<langle>c\<rangle> \<triangleright> x. B \<triangleleft> \<langle>x\<rangle>) \<rightarrow>\<lparr>\<alpha>\<rparr> P"
proof
  assume "\<nu> c. ((c \<noteq> a) ? \<langle>c\<rangle> \<triangleleft> X \<parallel> \<langle>c\<rangle> \<triangleright> x. B \<triangleleft> \<langle>x\<rangle>) \<rightarrow>\<lparr>\<alpha>\<rparr> P"
  then show False
  proof cases
    case opening
    from opening(4) show False
    proof cases
      case parallel_left
      from parallel_left(2) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case parallel_right
      from parallel_right(2) show False
        by cases
    qed
  next
    case new_channel
    from new_channel(2) show False
    proof cases
      case communication_ltr
      from communication_ltr(3) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case communication_rtl
      from communication_rtl(4) show False
        by cases
    next
      case parallel_left
      from parallel_left(2) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case parallel_right
      from parallel_right(2) show False
        by cases auto
    qed
  qed
qed

lemma other_channel_exists:
  fixes a :: chan
  obtains b where "b \<noteq> a"
proof -
  obtain c ::chan and d :: chan where "c \<noteq> d"
    using more_than_one_channel
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
  shows "\<not> \<nu> c. ((c = a) ? B \<triangleleft> X \<parallel> (c \<noteq> a) ? B \<triangleleft> X) \<rightarrow>\<lparr>\<alpha>\<rparr> P"
proof
  obtain d :: chan where "d \<noteq> a"
    using other_channel_exists .
  assume "\<nu> c. ((c = a) ? B \<triangleleft> X \<parallel> (c \<noteq> a) ? B \<triangleleft> X) \<rightarrow>\<lparr>\<alpha>\<rparr> P"
  moreover have "\<not> (\<lambda>e. ((shd e = a) ? B \<triangleleft> X \<parallel> (shd e \<noteq> a) ? B \<triangleleft> X) (stl e)) \<rightarrow>\<lparr>\<alpha>\<rparr> P" for \<alpha> and P
  proof
    assume "(\<lambda>e. ((shd e = a) ? B \<triangleleft> X \<parallel> (shd e \<noteq> a) ? B \<triangleleft> X) (stl e)) \<rightarrow>\<lparr>\<alpha>\<rparr> P"
    then show False
    proof cases
      case communication_ltr
      from communication_ltr(3) and \<open>d \<noteq> a\<close> show False
        by cases (auto dest: fun_cong [where x = "d ## undefined"])
    next
      case communication_rtl
      from communication_rtl(4) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    next
      case parallel_left
      from parallel_left(2) and \<open>d \<noteq> a\<close> show False
        by cases (auto dest: fun_cong [where x = "d ## undefined"])
    next
      case parallel_right
      from parallel_right(2) show False
        by cases (auto dest: fun_cong [where x = "a ## undefined"])
    qed
  qed
  ultimately show False
    by cases simp_all
qed

end
