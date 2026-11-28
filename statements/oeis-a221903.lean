import Mathlib

/-!
# A221903: Primes of the form 2*n^2 + 42*n + 19.

Source: https://oeis.org/A221903
Credit: @cjchaffin

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime; in other words, these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `2*n^2 + 42*n + 19` with `n ≥ 1`: the OEIS Mathematica and
  Magma programs both let `n` run from 1, and the data starts at a value for a positive `n`.
  The value at `n = 0` is the prime `19`, which is not a term (and `2^19 - 1` is prime).
-/

namespace OMA.S_oeis_a221903

/-- The quadratic `2*n^2 + 42*n + 19`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 42 * n + 19

theorem main : ∀ n : ℕ, 1 ≤ n → (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a221903
