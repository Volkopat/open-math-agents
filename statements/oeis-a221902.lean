import Mathlib

/-!
# A221902: Primes of the form 2*n^2 + 10*n + 3.

Source: https://oeis.org/A221902
Credit: @cjchaffin

Conjecture (stated on the OEIS page): After the first term, `2^a(n) - 1` is not prime; in other words, these primes (except 31) are included in A054723.

Conventions:
- The terms `a(n)` are the primes `2*n^2 + 10*n + 3` with `n ≥ 1`: the OEIS Mathematica and
  Magma programs both let `n` run from 1, and the data starts at a value for a positive `n`.
  The value at `n = 0` is the prime `3`, which is not a term (and `2^3 - 1` is prime).
- The excluded first term `31` becomes the hypothesis `f n ≠ 31` (`2^31 - 1` is prime).
-/

namespace OMA.S_oeis_a221902

/-- The quadratic `2*n^2 + 10*n + 3`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 10 * n + 3

theorem main : ∀ n : ℕ, 1 ≤ n → (f n).Prime → f n ≠ 31 → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a221902
