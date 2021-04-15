theory Timing
imports Main
begin

type_synonym slot = nat

abbreviation (input) genesis_slot :: slot where
  "genesis_slot \<equiv> 0"

end
