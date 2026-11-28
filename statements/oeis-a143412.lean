import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.Polynomial.Chebyshev

open MeasureTheory ProbabilityTheory

namespace OMA.S_oeis_a143412

/-- OEIS A143412, with its index starting at zero. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => 4 * (2 * n + 3) * a (n + 1) + a n

/-- A143412 is the expectation of the Chebyshev polynomial `U` of degree `2 * n`
evaluated at a standard normal random variable. Source: https://oeis.org/A143412. -/
theorem main : ∀ n : ℕ,
    (∫ x : ℝ, (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x ∂(gaussianReal 0 1)) =
      (a n : ℝ) := by
  sorry

end OMA.S_oeis_a143412
