import Mathlib

/-!
# A243889: Primes of the form 2*n^2+30*n+13.

Source: https://oeis.org/A243889
Credit: @cjchaffin

Conjecture (stated on the OEIS page): except 2281, `2^a(n) - 1` is not prime; in other words,
these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `p = 2*n^2 + 30*n + 13` with `n ≥ 1`, as in the OEIS Mathematica
  and Magma programs, which both let `n` run from 1. The value at `n = 0` is `13`, which is prime
  but is not a term: the data begins at the value for a positive `n`.
- The exception `2281` is kept as a hypothesis `f n ≠ 2281`, so the conjecture says nothing about it (`2^2281 - 1` is a Mersenne prime).
-/

namespace OMA.S_oeis_a243889

/-- The quadratic `2*n^2 + 30*n + 13`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 30 * n + 13

theorem main : ∀ n : ℕ, 1 ≤ n → (f n).Prime → f n ≠ 2281 → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a243889
