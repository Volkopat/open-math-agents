import FormalConjectures.Wikipedia.Bloch

-- Reduction Bloch.blochConstant_exact_value.R1 of Bloch and Landau constants — blochConstant exact value
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Bloch_blochConstant_exact_value_R1

def H1 : Prop :=
  Bloch.blochConstant ≤
    Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
      (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3))

def H2 : Prop :=
  Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
      (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) ≤
    Bloch.blochConstant

theorem main : H1 → H2 → type_of% @Bloch.blochConstant_exact_value := by
  intro h1 h2
  exact le_antisymm h1 h2

end OMA.R_Bloch_blochConstant_exact_value_R1
