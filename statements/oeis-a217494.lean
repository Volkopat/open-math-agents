import Mathlib

/-!
# A217494: Primes of the form 2*n^2 + 34*n + 15.

Source: https://oeis.org/A217494
Credit: @cjchaffin

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime; in other words, these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `2*n^2 + 34*n + 15`. We take `n : ℕ`. Whether `n` starts
  at 0 or 1 makes no difference, because the value `15` at `n = 0` is not prime.
- Integer `n < 0` gives no new primes: the polynomial is unchanged by `n ↦ -17 - n`, and for
  `-17 < n < 0` its value is negative.
-/

namespace OMA.S_oeis_a217494

/-- The quadratic `2*n^2 + 34*n + 15`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 34 * n + 15

theorem main : ∀ n : ℕ, (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a217494
