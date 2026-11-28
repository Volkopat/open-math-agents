import Mathlib

/-!
# A392116: a(n) = floor(prime(n + 1) / 5) - floor(prime(n) / 5)

Source: https://oeis.org/A392116

Conjecture (OEIS A392116):
Every nonnegative integer occurs in the sequence `a(n) = ⌊prime(n + 1) / 5⌋ - ⌊prime(n) / 5⌋`
for `n ≥ 1`.

Conventions:
- Offset: `1`; first terms: `0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, ...`.
- `Nat.nth Nat.Prime (n - 1)` is `prime(n)` (1-indexed) and `Nat.nth Nat.Prime n` is
  `prime(n + 1)` for `n ≥ 1`. Since `prime(n) < prime(n + 1)`, `ℕ` subtraction has no underflow.
-/

namespace OMA.S_oeis_a392116

/-- `a(n) = floor(prime(n + 1) / 5) - floor(prime(n) / 5)` for `n ≥ 1` (OEIS A392116). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n / 5 - Nat.nth Nat.Prime (n - 1) / 5

/-- Conjecture: every nonnegative integer occurs as `a(n)` for some `n ≥ 1`. -/
theorem main :
    ∀ m : ℕ, ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a392116
