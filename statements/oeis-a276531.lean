import Mathlib

/-!
# A276531: a(n) = (a(n-1)*a(n-5) + a(n-2)*a(n-3)*a(n-4)) / a(n-6) is always an integer

Source: https://oeis.org/A276531

A276531 (offset 0): `a(n) = (a(n-1) * a(n-5) + a(n-2) * a(n-3) * a(n-4)) / a(n-6)`, with
`a(0) = a(1) = a(2) = a(3) = a(4) = a(5) = 1`: 1, 1, 1, 1, 1, 1, 2, 3, 5, 11, 41, 247, 1498,
39629, 3121233, 1344630757, …  The entry describes it as a generalization of Dana Scott's
sequence A048736.

Conjecture (Seiichi Manyama, Nov 16 2016): `a(n)` is an integer for all `n`. The entry notes
that it has been checked by computer for `0 ≤ n ≤ 50`.

Conventions:
- The recurrence is run in `ℚ` with exact rational division, so the question whether the terms
  are integers is meaningful. All terms are positive (by induction: sums and products of
  positive rationals divided by a positive rational), so no division by zero occurs.
- `a(n)` is an integer when it equals the cast of some `z : ℤ`.
-/

namespace OMA.S_oeis_a276531

/-- A276531 as a sequence of rational numbers: six initial ones, then
`a(n+6) = (a(n+5)*a(n+1) + a(n+4)*a(n+3)*a(n+2)) / a(n)`. -/
def a : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | (n + 6) => (a (n + 5) * a (n + 1) + a (n + 4) * a (n + 3) * a (n + 2)) / a n

theorem main : ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a276531
