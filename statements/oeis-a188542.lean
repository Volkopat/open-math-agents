import Mathlib

/-!
# A188542: number of primes between `n^3 - n` and `n^3 + n`

Source: https://oeis.org/A188542
Credit: @Lenqth

A188542 counts the primes `p` with `n^3 - n ≤ p ≤ n^3 + n` (the OEIS entry includes the end
points; this matters only for `n = 1`, where the range `[0, 2]` contains the prime `2`).

Formalizes the conjecture in the comments of A188542: the sequence contains no zeros, i.e. for
every `n ≥ 1` there is a prime in `[n^3 - n, n^3 + n]` (offset 1; verified up to `n = 100000`
according to the entry).
-/

namespace OMA.S_oeis_a188542

/-- For every `n ≥ 1` there is a prime `p` with `n^3 - n ≤ p ≤ n^3 + n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 - n ≤ p ∧ p ≤ n ^ 3 + n := by
  sorry

end OMA.S_oeis_a188542
