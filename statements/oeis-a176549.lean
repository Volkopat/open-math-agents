import Mathlib

/-!
# A176549: Primes of the form 2*n^2+6*n+1.

Source: https://oeis.org/A176549
Credit: @cjchaffin

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime; in other words, these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `2*n^2 + 6*n + 1`. We take `n : ℕ`. Whether `n` starts
  at 0 or 1 makes no difference, because the value `1` at `n = 0` is not prime.
- Integer `n < 0` gives no new primes: the polynomial is unchanged by `n ↦ -3 - n`, and for
  `-3 < n < 0` its value is negative.
-/

namespace OMA.S_oeis_a176549

/-- The quadratic `2*n^2 + 6*n + 1`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 6 * n + 1

theorem main : ∀ n : ℕ, (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a176549
