section \<open>Square Numbers Server\<close>

text \<open>
  Imagine a community effort whose goal is to find large square numbers. Arbitrary people
  use their computing power to engage in square number search. We implement a server that
  accepts submissions of found square numbers and announces any new record.
\<close>

theory Square_Numbers_Server
  imports Chi_Calculus.Typed_Processes "HOL-Library.Discrete" "HOL-Library.BNF_Corec"
begin

text \<open>
  We define a special data type for the messages that are sent or received along channels.
\<close>

type_synonym Submission = "nat \<times> nat"

type_synonym Announcement = nat

(*
  It might be better to introduce dedicated data types for \<open>Submission\<close> and \<open>Announcement\<close>. At the
  moment we use type synonyms, because we do not have to instantiate the \<open>countable\<close> class this way.
*)

text \<open>
  We define names to be composed by a tag indicating the process to be invoked plus the required
  arguments for the process.
\<close>

text \<open>
  Now, we implement the server process.
\<close>

value "case (1 :: nat, 2 :: nat, 3 :: nat) of (a, b, c) \<Rightarrow> a + b + c"

corec serve :: "[nat, Submission channel, Announcement channel] \<Rightarrow> process"
where
  "serve record submissions announcements =
    submissions \<triangleright>\<degree> m. (
      case m of (square_num, square_root) \<Rightarrow>
        if square_num > record \<and> square_num = square_root\<^sup>2
        then
           announcements \<triangleleft>\<degree> square_num
          \<parallel>
          serve square_num submissions announcements
        else
          serve record submissions announcements
      )"

primcorec square_num_server :: "Submission channel \<Rightarrow> Announcement channel \<Rightarrow> process"
where
  "square_num_server submissions announcements = serve 0 submissions announcements"

text \<open>
  The following is a possible implementation of a client process which sends a list of square
  numbers to the server process and receives announcements from it.
\<close>

fun submit_numbers :: "nat list \<Rightarrow> Submission channel \<Rightarrow> process"
where
  "submit_numbers numbers submissions = (
    case numbers of
      []       \<Rightarrow> \<zero> |
      (n # ns) \<Rightarrow>
        submissions \<triangleleft>\<degree> (n, Discrete.sqrt n)
        \<parallel>
        submit_numbers ns submissions)"

primcorec receive_announcements :: "Announcement channel \<Rightarrow> process"
where
  "receive_announcements announcements =
    announcements \<triangleright>\<degree> a. receive_announcements announcements"

definition square_num_client :: "nat list \<Rightarrow> Submission channel \<Rightarrow> Announcement channel \<Rightarrow> process"
where
  "square_num_client numbers submissions announcements \<equiv>
    submit_numbers numbers submissions \<parallel> receive_announcements announcements"

text \<open>
  Finally, we define an application comprised by a server and two clients.
\<close>

definition square_num_app :: process
where
  "square_num_app \<equiv> \<nu>\<degree>submissions. \<nu>\<degree>announcements. (
    square_num_server submissions announcements
    \<parallel>
    square_num_client [16,4,25] submissions announcements
    \<parallel>
    square_num_client [4,81] submissions announcements)"

end
