import Mathlib

/-!
# A217497: Primes of the form 2*n^2 + 54*n + 25.

Source: https://oeis.org/A217497
Credit: @sntntHb

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime for every term `a(n)`; in other
words, these primes are included in A054723.

Conventions:
- The terms are the primes `p = 2*n^2 + 54*n + 25`. We take `n : ℕ`. Allowing all integers `n`
  gives no new primes: the polynomial is symmetric under `n ↦ -27 - n`
  (`2 * (2*n^2 + 54*n + 25) + 679 = (2*n + 27)^2`), so every `n ≤ -27` gives the same value as
  `-27 - n ≥ 0`, and for `-26 ≤ n ≤ -1` the value is negative.
-/

namespace OMA.S_oeis_a217497

/-- The quadratic `2*n^2 + 54*n + 25`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 54 * n + 25

theorem main : ∀ n : ℕ, (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a217497
