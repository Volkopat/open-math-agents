import Mathlib

/-!
# OEIS A016069: numbers whose square has exactly two distinct digits

Source: https://oeis.org/A016069
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A016069 lists the `k` such that `k²` has exactly two distinct (decimal) digits, in increasing
order: `4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 20, 21, 22, 26, 30, 38, 88, 100, …` (offset 1).
Conjecture (OEIS entry): `a(n) = ((n-1) mod 3 + 1) · 10^(⌈n/3⌉ - 7)` for `n ≥ 34`.

Conventions:
* `a n` (`n ≥ 1`) is `Nat.nth P (n - 1)` for the predicate `P k := (digits of k²).toFinset` has
  two elements.
-/

namespace OMA.S_oeis_a016069

/-- `k²` has exactly two distinct decimal digits. -/
def P (k : ℕ) : Prop := (Nat.digits 10 (k ^ 2)).toFinset.card = 2

/-- The `n`-th term (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- For `n ≥ 34`, `a(n) = ((n-1) mod 3 + 1) · 10^(⌈n/3⌉ - 7)`. -/
theorem main : ∀ n : ℕ, 34 ≤ n → a n = ((n - 1) % 3 + 1) * 10 ^ ((n + 2) / 3 - 7) := by
  sorry

end OMA.S_oeis_a016069
