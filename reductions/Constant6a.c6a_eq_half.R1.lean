import FormalConjectures.OptimizationConstants.«6a»

/-! Splitting the Frankl union-closed sets conjecture on the constant C6a into
the proved Frankl upper bound and the open sharp lower bound. -/

-- Reduction Constant6a.c6a_eq_half.R1 of the Frankl union-closed sets conjecture
-- Tao optimization constant 6a: C6a = 1/2.
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Constant6a_c6a_eq_half_R1

-- The already proved Frankl upper bound (upstream theorem c6a_upper_bound).
def H1 : Prop := Constant6a.C6a ≤ 1 / 2

-- The genuinely open sharp lower bound for the union-closed sets constant.
def H2 : Prop := 1 / 2 ≤ Constant6a.C6a

theorem main : H1 → H2 → type_of% @Constant6a.c6a_eq_half := by
  intro hupper hlower
  exact le_antisymm hupper hlower

end OMA.R_Constant6a_c6a_eq_half_R1
