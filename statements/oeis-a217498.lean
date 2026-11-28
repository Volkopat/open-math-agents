import Mathlib

/-!
# A217498: Primes of the form 2*n^2 + 58*n + 27.

Source: https://oeis.org/A217498
Credit: @cjchaffin

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime; in other words, these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `2*n^2 + 58*n + 27`. We take `n : ℕ`. Whether `n` starts
  at 0 or 1 makes no difference, because the value `27` at `n = 0` is not prime.
- Integer `n < 0` gives no new primes: the polynomial is unchanged by `n ↦ -29 - n`, and for
  `-29 < n < 0` its value is negative.
-/

namespace OMA.S_oeis_a217498

/-- The quadratic `2*n^2 + 58*n + 27`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 58 * n + 27

theorem main : ∀ n : ℕ, (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a217498
