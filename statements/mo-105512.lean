import Mathlib

namespace OMA.S_mo_105512

open MeasureTheory

abbrev Unitary (n : ℕ) := ↥(Matrix.unitaryGroup (Fin n) ℂ)
abbrev Orthogonal (n : ℕ) := ↥(Matrix.orthogonalGroup (Fin n) ℝ)

/-- Equal laws of the full eigenvalue multisets after adjoining one copy of
minus one to the unitary product. -/
theorem main :
    ∀ n : ℕ, 0 < n →
    letI : MeasurableSpace (Unitary n) := borel (Unitary n)
    letI : MeasurableSpace (Orthogonal (n + 1)) := borel (Orthogonal (n + 1))
    ∀ (μ : Measure (Unitary n)) (ν : Measure (Orthogonal (n + 1))),
      μ.IsHaarMeasure → IsProbabilityMeasure μ →
      ν.IsHaarMeasure → IsProbabilityMeasure ν →
      let negative : Set (Orthogonal (n + 1)) := {O | O.val.det = -1}
      let unitaryCoefficients (U : Unitary n) (k : Fin (n + 2)) :=
        ((Polynomial.X + 1) * (U.val * U.val.map (star : ℂ → ℂ)).charpoly).coeff k.val
      let orthogonalCoefficients (O : Orthogonal (n + 1)) (k : Fin (n + 2)) :=
        (O.val.map (fun x : ℝ => (x : ℂ))).charpoly.coeff k.val
      Measure.map unitaryCoefficients μ =
        Measure.map orthogonalCoefficients ((ν negative)⁻¹ • ν.restrict negative) := by
  sorry

end OMA.S_mo_105512
