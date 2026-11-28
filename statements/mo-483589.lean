import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

namespace OMA.S_mo_483589

universe u

/-- Finite groups have faithful projective representations over commutative
rings in dimension at most a universal constant times the log of the order. -/
theorem main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Type u) [Group G] [Finite G], 2 ≤ Nat.card G →
        ∃ (R : Type u) (_ : CommRing R) (d : ℕ),
          0 < d ∧ (d : ℝ) ≤ C * Real.log (Nat.card G : ℝ) ∧
            ∃ ρ : G →* Matrix.ProjGenLinGroup (Fin d) R, Function.Injective ρ := by
  sorry

end OMA.S_mo_483589
