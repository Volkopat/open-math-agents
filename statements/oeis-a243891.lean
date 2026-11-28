import Mathlib

/-!
# A243891: Primes of the form 2*n^2+62*n+29.

Source: https://oeis.org/A243891
Credit: @cjchaffin

Conjecture (stated on the OEIS page): except 4253, `2^a(n) - 1` is not prime; in other words,
these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `p = 2*n^2 + 62*n + 29` with `n ≥ 1`, as in the OEIS Mathematica
  and Magma programs, which both let `n` run from 1. The value at `n = 0` is `29`, which is prime
  but is not a term: the data begins at the value for a positive `n`.
- The exception `4253` is kept as a hypothesis `f n ≠ 4253`, so the conjecture says nothing about it (`2^4253 - 1` is a Mersenne prime).
-/

namespace OMA.S_oeis_a243891

/-- The quadratic `2*n^2 + 62*n + 29`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 62 * n + 29

theorem main : ∀ n : ℕ, 1 ≤ n → (f n).Prime → f n ≠ 4253 → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a243891
