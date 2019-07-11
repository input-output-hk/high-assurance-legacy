theory Equivalences
  imports Main "HOL-Eisbach.Eisbach"
begin

named_theorems equivalence_simp_goal_preparation and equivalence_simp

method equivalence_simp = (
  simp only: equivalence_simp_goal_preparation [THEN sym] id_def comp_def;
    simp only: equivalence_simp [transferred]
)

end
