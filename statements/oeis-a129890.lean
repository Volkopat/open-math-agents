import Mathlib

/-!
# A129890: a(n) = (2*n+2)!! - (2*n+1)!!.

Source: https://oeis.org/A129890
Credit: @agchua

Peter Bala (Jul 06 2025), in the formula section of A129890:
  Conjecture: a(n) = (2*n + 2)*(2*n + 2)! * Sum_{k >= 1} (-1)^(k+1)/Product_{j = 0..n+1} (k + 2*j)
  [added Dec 03 2025: this identity can be verified using Maple's sum command]. - _Peter Bala_, Jul 06 2025
A129890 has offset 0, so the claim is stated for all n >= 0. Below the summation index k >= 1 of
the series is written as k + 1 with k >= 0, and the series is the real sum `tsum` (its terms are
at most 1/(k+1)^2 in absolute value, so it converges absolutely).
-/

namespace OMA.S_oeis_a129890

/-- A129890: a(n) = (2n+2)!! - (2n+1)!!. -/
def a (n : ℕ) : ℤ := ((2 * n + 2).doubleFactorial : ℤ) - ((2 * n + 1).doubleFactorial : ℤ)

/-- Bala's conjecture:
a(n) = (2n+2) (2n+2)! Sum_{k >= 1} (-1)^(k+1) / Product_{j=0..n+1} (k + 2j). -/
theorem main : ∀ n : ℕ, (a n : ℝ) = (2 * n + 2) * ((2 * n + 2).factorial : ℝ) *
    ∑' k : ℕ, (-1 : ℝ) ^ ((k + 1) + 1) /
      ∏ j ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℝ) + 2 * j) := by
  sorry

end OMA.S_oeis_a129890
