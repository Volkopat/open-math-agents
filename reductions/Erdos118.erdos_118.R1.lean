import FormalConjectures.ErdosProblems.«118»

-- Reduction Erdos118.erdos_118.R1 of Erdős Problem 118
-- Credit: @expectfun
-- Larson's counterexample ω^{ω²}, split into the positive and negative relations.
-- The implication is the only part proved here.

namespace OMA.R_Erdos118_erdos_118_R1

/-- Larson (2000): $\omega^{\omega^2} \to (\omega^{\omega^2}, 3)^2$ at universe 0. -/
def H1 : Prop :=
  Erdos118.OrdinalRamsey.{0}
    (Ordinal.omega0.{0} ^ Ordinal.omega0.{0} ^ (2 : Ordinal.{0}))
    (Ordinal.omega0.{0} ^ Ordinal.omega0.{0} ^ (2 : Ordinal.{0}))
    (3 : Ordinal.{0})

/-- Larson (2000): $\omega^{\omega^2} \not\to (\omega^{\omega^2}, 5)^2$ at universe 0. -/
def H2 : Prop :=
  ¬ Erdos118.OrdinalRamsey.{0}
      (Ordinal.omega0.{0} ^ Ordinal.omega0.{0} ^ (2 : Ordinal.{0}))
      (Ordinal.omega0.{0} ^ Ordinal.omega0.{0} ^ (2 : Ordinal.{0}))
      (5 : Ordinal.{0})

theorem main : H1 → H2 → type_of% @Erdos118.erdos_118 := by
  intro hPos hNeg h
  exact hNeg (h (Ordinal.omega0.{0} ^ Ordinal.omega0.{0} ^ (2 : Ordinal.{0})) hPos 5 (by omega))

end OMA.R_Erdos118_erdos_118_R1
