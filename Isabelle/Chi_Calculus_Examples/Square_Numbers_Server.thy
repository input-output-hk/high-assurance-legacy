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
  | Args nat 'chan 'chan


text \<open>
  We define names to be just plain @{typ string}'s since we want to look up process definitions
  in the environment by their names.
\<close>

type_synonym name = string

text \<open>
  Now, we implement the server process.
\<close>

fun serve :: "'chan val \<Rightarrow> (name, 'chan, 'chan val) process" where
"serve (Args record submissions announcements) =
  \<cdot>submissions \<triangleright> m. (
    case m of SquareNumSubmission square_num root \<Rightarrow>
      if square_num > record \<and> square_num = root\<^sup>2
      then
         \<cdot>announcements \<triangleleft> (Announcement square_num)
        \<parallel>
        \<langle>''serve''\<rangle> (Args square_num submissions announcements)
      else
        \<langle>''serve''\<rangle> (Args record submissions announcements)
    )"

definition square_num_server :: "'chan \<Rightarrow> 'chan \<Rightarrow> (name, 'chan, 'chan val) process" where
"square_num_server submissions announcements = serve (Args 0 submissions announcements)"

end
