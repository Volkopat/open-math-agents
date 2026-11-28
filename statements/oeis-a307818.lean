import Mathlib

/-!
# A307818: Numbers k such that A240718(k) = 0

Source: https://oeis.org/A307818

Conjecture (OEIS A307818):
Let `A240718(k)` be the number of unordered decompositions of `2 * k` as the sum of
two primes `p + q` such that `min(p, q) < sqrt(2 * k - 2)`.
Then `31637` is the last integer `k` with `A240718(k) = 0`; that is, for every
`k > 31637`, there exist primes `p` and `q` such that `p + q = 2 * k` and
`p ^ 2 < 2 * k - 2`.

Conventions:
- For `k = 31637`, `2 * k = 63274` has no prime `p < sqrt(63272)` with `63274 - p` prime
  (`A240718(31637) = 0`).
- `p < sqrt(2 * k - 2)` is expressed cleanly over `ℕ` as `p ^ 2 < 2 * k - 2`.
-/

namespace OMA.S_oeis_a307818

/-- Conjecture: `31637` is the last term of A307818; for every `k > 31637`, `2 * k` is
the sum of two primes `p + q` with `p ^ 2 < 2 * k - 2`. -/
theorem main :
    ∀ k : ℕ, 31637 < k →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * k ∧ p ^ 2 < 2 * k - 2 := by
  sorry

end OMA.S_oeis_a307818
