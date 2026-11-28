import Mathlib

open MeasureTheory

namespace OMA.S_mo_344216

/-- The Gaussian inequality for a convex real function of at most
linear growth, under its normalized exponential change of measure. -/
theorem main :
    ∀ (d : ℕ) (φ : EuclideanSpace ℝ (Fin d) → ℝ),
      ConvexOn ℝ Set.univ φ →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ x, |φ x| ≤ K * (1 + ‖x‖)) →
      let γ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))
      (∫ x, Real.exp (φ x) ∂γ) = 1 →
      let μ := γ.withDensity (fun x => ENNReal.ofReal (Real.exp (φ x)))
      2 * (∫ x, φ x ∂μ) ≤ ∫ x, (∫ y, (φ x - φ y) ^ 2 ∂μ) ∂μ := by
  sorry

end OMA.S_mo_344216
