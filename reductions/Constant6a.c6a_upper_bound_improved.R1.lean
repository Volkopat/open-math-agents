import FormalConjectures.OptimizationConstants.«6a»

-- Reduction Constant6a.c6a_upper_bound_improved.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Constant6a_c6a_upper_bound_improved_R1

def H1 : Prop := Constant6a.C6a ≤ 1 / 2

def H2 : Prop := Constant6a.C6a ≠ 1 / 2

theorem main : H1 → H2 → type_of% @Constant6a.c6a_upper_bound_improved := by
  intro h1 h2
  exact lt_of_le_of_ne h1 h2

end OMA.R_Constant6a_c6a_upper_bound_improved_R1
