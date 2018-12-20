section \<open>Utilities\<close>

theory Utilities
  imports
    Chi_Calculus.Processes
    Chi_Calculus.Proper_Weak_Bisimulation
begin

(* TODO: Prove it. *)
lemma internal_communication: "\<nu> c. (c \<triangleleft> y \<parallel> c \<triangleright> x. P x) \<approx>\<^sub>\<sharp> \<nu> c. P y"
  sorry

lemma weak_proper_parallel_scope_redundancy: "\<nu> c. (p \<parallel> P c) \<approx>\<^sub>\<sharp> p \<parallel> \<nu> c. P c"
  (* FIXME: Find a nicer proof. *)
  by (smt
      weak_proper_scope_redundancy
      weak_proper_bisim_elim2
      weak_proper_bisim_transitivity
      weak_proper_new_channel_preservation
      weak_proper_parallel_commutativity
      weak_proper_parallel_scope_extension)

end
