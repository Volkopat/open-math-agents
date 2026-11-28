import Mathlib

/-!
# A243957: Primes of the form 2*n^2+66*n+31.

Source: https://oeis.org/A243957
Credit: @cjchaffin

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime; in other words,
these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `p = 2*n^2 + 66*n + 31` with `n ≥ 1`, as in the OEIS Mathematica
  and Magma programs, which both let `n` run from 1. The value at `n = 0` is `31`, which is prime
  but is not a term: the data begins at the value for a positive `n`.
-/

namespace OMA.S_oeis_a243957

/-- The quadratic `2*n^2 + 66*n + 31`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 66 * n + 31

theorem main : ∀ n : ℕ, 1 ≤ n → (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a243957
