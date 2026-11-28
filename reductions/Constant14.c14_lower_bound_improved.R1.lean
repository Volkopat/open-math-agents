import FormalConjectures.OptimizationConstants.«14»

-- Reduction Constant14.c14_lower_bound_improved.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Constant14_c14_lower_bound_improved_R1

def H1 : Prop := 6 ≤ Constant14.C14

def H2 : Prop := 6 ≠ Constant14.C14

theorem main : H1 → H2 → type_of% @Constant14.c14_lower_bound_improved := by
  intro h1 h2
  exact lt_of_le_of_ne h1 h2

end OMA.R_Constant14_c14_lower_bound_improved_R1
