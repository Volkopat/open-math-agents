import Mathlib

/-!
# A253238: Number of ways to write n as a sum of a perfect power (>1) and a prime.

Source: https://oeis.org/A253238
Credit: @sobrien032

`a n` counts the perfect powers `q > 1`, that is `q = m ^ k` with `m ≥ 2` and `k ≥ 2`, such that
`n - q` is prime: each such `q` is one way to write `n = q + p` with `p` prime. A perfect power is
counted once, however many ways it can be written as `m ^ k`, as in the entry's data. The entry
(Eric Chen, 2015) conjectures that `a n > 1` for all `n > 3319`.
-/

namespace OMA.S_oeis_a253238

/-- The number of ways to write `n` as a perfect power greater than `1` plus a prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  {q : ℕ | q < n ∧ (∃ m k : ℕ, 2 ≤ m ∧ 2 ≤ k ∧ m ^ k = q) ∧ (n - q).Prime}.ncard

/-- Conjecture: `a n > 1` for all `n > 3319`. -/
theorem main : ∀ n : ℕ, 3319 < n → 1 < a n := by
  sorry

end OMA.S_oeis_a253238
