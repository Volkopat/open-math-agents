import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

open MeasureTheory
open scoped BigOperators

namespace OMA.S_mo_116134

/-- Coefficient vectors for which the polynomial is small throughout the indicated arc. -/
def smallOnArc (n : ℕ) (C r ell m : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {a | ∀ θ : ℝ, |θ| < C * ell →
    ‖∑ k : Fin (n + 1),
        (a k : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ k.val‖ ≤
      Real.rpow (n : ℝ) (-C) * Real.rpow ell (C * m) *
        ∑ k : Fin (n + 1), |a k| * r ^ k.val}

/-- The proposed polynomial tail estimate for iid real coefficients with no atom at zero. -/
theorem main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (m r ell : ℝ) (μ : ProbabilityMeasure ℝ),
        2 ≤ n → 2 ≤ m → 0 < r → 0 < ell → ell < 1 →
          (μ : Measure ℝ) ({0} : Set ℝ) = 0 →
            (ProbabilityMeasure.pi (fun _ : Fin (n + 1) => μ) :
              Measure (Fin (n + 1) → ℝ)) (smallOnArc n C r ell m) ≤
                ENNReal.ofReal (Real.rpow (n : ℝ) (-m)) := by
  sorry

end OMA.S_mo_116134
