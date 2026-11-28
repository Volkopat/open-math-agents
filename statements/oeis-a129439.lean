import Mathlib

/-!
# Integrality of the generalized binomial coefficients A129439

Source: https://oeis.org/A129439
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a129439

/-- Cumulative product of all divisors of the positive integers through n (A092143). -/
def D (n : ℕ) : ℕ := ∏ m ∈ Finset.range (n+1), ∏ d ∈ m.divisors, d

theorem main : ∀ n k : ℕ, k ≤ n → D (n-k) * D k ∣ D n := by
  sorry

end OMA.S_oeis_a129439
