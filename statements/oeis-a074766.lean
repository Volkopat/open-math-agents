import Mathlib

/-!
# A074766: a(n) = prime(2n) - 2*prime(n) - n.

Source: https://oeis.org/A074766
Credit: @EmircanEsen

Conjecture (OEIS A074766): p(2n) - 2p(n) < 2n for all n.

Formalization notes:
* `prime k` is the `k`-th prime with OEIS indexing, `prime 1 = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
  The sequence has offset 1, so "for all n" means every `n ≥ 1`.
* The difference `p(2n) - 2p(n)` can be negative (`n = 1`: `3 - 4 = -1`), so it is computed in `ℤ`.
  In terms of the sequence the conjecture says `a(n) < n`.
* Checked numerically for `n < 74466`: the largest value of `(p(2n) - 2p(n)) / n` there is `1.875`.
-/

namespace OMA.S_oeis_a074766

/-- The `k`-th prime with OEIS indexing: `prime 1 = 2`, `prime 2 = 3`, …. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A074766, offset 1: `a n = prime (2n) - 2 * prime n - n`. -/
noncomputable def a (n : ℕ) : ℤ := (prime (2 * n) : ℤ) - 2 * prime n - n

/-- For every `n ≥ 1`, `p(2n) - 2 p(n) < 2n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (prime (2 * n) : ℤ) - 2 * prime n < 2 * n := by
  sorry

end OMA.S_oeis_a074766
