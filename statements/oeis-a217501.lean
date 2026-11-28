import Mathlib

/-!
# A217501: Primes of the form 2*n^2 + 78*n + 37.

Source: https://oeis.org/A217501
Credit: @cjchaffin

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime; in other words, these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `2*n^2 + 78*n + 37` with `n ≥ 0`, as in the OEIS programs
  (`n` runs from 0); the first term `37` is the value at `n = 0`.
- Integer `n < 0` gives no new primes: the polynomial is unchanged by `n ↦ -39 - n`, and for
  `-39 < n < 0` its value is negative.
-/

namespace OMA.S_oeis_a217501

/-- The quadratic `2*n^2 + 78*n + 37`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 78 * n + 37

theorem main : ∀ n : ℕ, (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a217501
