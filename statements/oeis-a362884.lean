import Mathlib

/-!
# A362884: a(n) = (a(n-1)*a(n-2)*a(n-3) + 64)/(4*a(n-4))

Source: https://oeis.org/A362884

A362884 (offset 0): `a(n) = (a(n-1)*a(n-2)*a(n-3) + 64)/(4*a(n-4))` with
`a(0) = a(2) = a(3) = 2` and `a(1) = 16`: 2, 16, 2, 2, 16, 2, 16, 72, 37, 5336, 222112,
152263946, …

The entry (Max Alekseyev, May 07 2023) states two conjectures:
1. All terms are integer.
2. `a(n)` is never divisible by 64.

Both are stated together: every term equals an integer `z`, and that integer is not divisible
by 64.

Conventions: the recurrence is run in `ℚ` with exact rational division, so that the question
whether the terms are integers is meaningful. All terms are positive (by induction), so no
division by zero occurs.
-/

namespace OMA.S_oeis_a362884

/-- A362884 as a sequence of rational numbers. -/
def a : ℕ → ℚ
  | 0 => 2
  | 1 => 16
  | 2 => 2
  | 3 => 2
  | (n + 4) => (a (n + 3) * a (n + 2) * a (n + 1) + 64) / (4 * a n)

theorem main : ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℚ) ∧ ¬ (64 : ℤ) ∣ z := by
  sorry

end OMA.S_oeis_a362884
