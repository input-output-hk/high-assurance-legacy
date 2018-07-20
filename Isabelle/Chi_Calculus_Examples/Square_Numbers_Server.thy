section \<open>Square Numbers Server\<close>

text \<open>
  Imagine a community effort whose goal is to find large square numbers. Arbitrary people
  use their computing power to engage in square number search. We implement a server that
  accepts submissions of found square numbers and announces any new record.
\<close>

theory Square_Numbers_Server
  imports Chi_Calculus.Processes
begin

text \<open>
  We define a special data type for the values that are sent or received along channels.
\<close>

datatype 'chan val =
    SquareNumSubmission nat nat
  | Announcement nat
  | Nothing

text \<open>
  We define names to be composed by a tag indicating the process to be invoked plus the required
  arguments for the process.
\<close>

datatype 'chan name =
    ServeInvoke nat 'chan 'chan

text \<open>
  Now, we implement the server process.
\<close>

fun serve :: "(nat \<times> 'chan \<times> 'chan) \<Rightarrow> ('chan name, 'chan, 'chan val) process"
where
  "serve (record, submissions, announcements) =
    \<cdot>submissions \<triangleright> m. (
      case m of SquareNumSubmission square_num square_root \<Rightarrow>
        if square_num > record \<and> square_num = square_root\<^sup>2
        then
           \<cdot>announcements \<triangleleft> Announcement square_num
          \<parallel>
          \<langle>ServeInvoke square_num submissions announcements\<rangle> Nothing
        else
          \<langle>ServeInvoke record submissions announcements\<rangle> Nothing
      )"

definition square_num_server :: "'chan \<Rightarrow> 'chan \<Rightarrow> ('chan name, 'chan, 'chan val) process"
where
  "square_num_server submissions announcements \<equiv> serve (0, submissions, announcements)"

end
