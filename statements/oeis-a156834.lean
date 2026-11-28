import Mathlib

/-!
# OEIS A156834

Source: https://oeis.org/A156834 (OEIS Foundation, CC BY-SA 4.0).
The conjecture in Gary W. Adamson's entry says that for `n > 1`, `a(n) = n`
exactly when `n` is prime. The defining divisor sum is the formula contributed by
Seiichi Manyama. Its terms use the Euler totient and a binomial coefficient.
-/

namespace OMA.S_oeis_a156834

/-- The divisor-sum formula for A156834. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d.totient * (d + n / d - 2).choose (d - 1)

/-- Adamson's conjecture characterizing prime indices. -/
theorem main : ∀ n : ℕ, 1 < n → (a n = n ↔ n.Prime) := by
  sorry

end OMA.S_oeis_a156834
