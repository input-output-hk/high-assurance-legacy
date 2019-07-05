theory Equivalences
  imports Main "HOL-Eisbach.Eisbach"
begin

named_theorems equivalence_goal_preparation and equivalence_simp

method equivalence_simp = (
  simp only: equivalence_goal_preparation [THEN sym];
    simp only: equivalence_simp [transferred]
)

end
