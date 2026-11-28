import Mathlib

/-!
# A261525: Smallest m such that A031131(m) = 2 * n

Source: https://oeis.org/A261525

Conjecture (OEIS A261525):
Let `A031131(m) = prime(m + 2) - prime(m)` for `m ≥ 1`. Then for every integer
`n > 1`, there exists `m ≥ 1` such that `prime(m + 2) - prime(m) = 2 * n`;
equivalently, `A261525(n)` is defined for all `n > 1`.

Conventions:
- Offset: `2` (`n ≥ 2`).
- First terms of A031131 (`m ≥ 1`): `3, 4, 6, 6, 8, 6, 6, 10, 8, 8, ...`
  (note `prime(3) - prime(1) = 5 - 2 = 3`, `prime(4) - prime(2) = 7 - 3 = 4`, ...).
- First terms of A261525 (`n ≥ 2`): `2, 3, 9, 8, 15, 23, 47, 29, 66, 114, 46, ...`.
- `Nat.nth Nat.Prime (m - 1)` is `prime(m)` (`1`-indexed) and `Nat.nth Nat.Prime (m + 1)`
  is `prime(m + 2)`.
-/

namespace OMA.S_oeis_a261525

/-- Conjecture: every even integer `2 * n` with `n > 1` occurs as `prime(m + 2) - prime(m)`
for some `m ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ m : ℕ, 1 ≤ m ∧ Nat.nth Nat.Prime (m - 1) + 2 * n = Nat.nth Nat.Prime (m + 1) := by
  sorry

end OMA.S_oeis_a261525
