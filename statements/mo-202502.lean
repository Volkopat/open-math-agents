import Mathlib.Probability.Moments.Basic

/-!
# MGF order and stochastic tail order

Source: https://mathoverflow.net/questions/202502
The source asks about a direct tail inequality. This statement tests the
standard interpretation of that phrase: first-order stochastic dominance
at every common threshold. The measures are the laws of the random variables.
All positive-argument MGFs are required to be finite via integrability.
-/

open MeasureTheory ProbabilityTheory Set

namespace OMA.S_mo_202502

theorem main : ∀ (μ ν : Measure ℝ),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    (∀ t : ℝ, 0 < t →
      Integrable (fun x : ℝ => Real.exp (t * x)) μ ∧
      Integrable (fun x : ℝ => Real.exp (t * x)) ν ∧
      mgf id μ t ≤ mgf id ν t) →
    ∀ x : ℝ, μ (Ioi x) ≤ ν (Ioi x) := by
  sorry

end OMA.S_mo_202502
