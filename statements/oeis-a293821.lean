import Mathlib

/-!
# OEIS A293821: quadrilaterals of perimeter n modulo rotation

Source: https://oeis.org/A293821
Credit: Sudharsan Rajendiran

A293821(n) is the number of integer-sided quadrilaterals having perimeter `n`, modulo rotations
but not reflections; the entry notes that a polygon is nondegenerate exactly when its longest side
is shorter than `n/2`. Colin Barker conjectured (Nov 2017) the g.f.
`x^3(1 - x^2 + 2x^3)/((1 - x)^4 (1 + x)^3 (1 + x^2))` and the closed form
`(1/96)(-3(-1 + (-1)^n + 4i(-i)^n - 4i i^n) + (7 - 15(-1)^n)n + 3(-1 + (-1)^n)n^2 + 2n^3)`,
`i = sqrt(-1)`. Both index the data from `3` (the g.f. starts at `x^3`, while the entry's offset is
`4`): the closed form at `n` gives the entry's term `a(n + 1)` (e.g. `n = 3, 4, 5, 6` give
`1, 1, 2, 4 = a(4), a(5), a(6), a(7)`). We state the closed form in this indexing, over `ℂ`, for all
`n ≥ 3` (i.e. for every term of the data).

Conventions: a quadrilateral is a side sequence `v : Fin 4 → ℕ` in cyclic order with positive sides,
sum `n` and `2 * v i < n` for all `i`; two are equal modulo rotation iff one is a cyclic shift of the
other.
-/

namespace OMA.S_oeis_a293821

/-- Integer-sided quadrilaterals with perimeter `n`: side sequences `v 0, v 1, v 2, v 3` (in cyclic
order) of positive integers with sum `n` and every side shorter than `n / 2` (equivalently, shorter
than the sum of the other three sides). -/
def Q (n : ℕ) : Finset (Fin 4 → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (n + 1)).filter
    (fun v => (∀ i, 0 < v i ∧ 2 * v i < n) ∧ ∑ i, v i = n)

open Classical in
/-- A293821(n): the number of such quadrilaterals modulo rotations (`w ~ v` iff
`w i = v (i + k)` for some `k`, indices mod 4), but not reflections. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Q n).image (fun v => (Q n).filter (fun w => ∃ k : Fin 4, w = fun i => v (i + k)))).card

open Complex in
theorem main : ∀ n : ℕ, 3 ≤ n →
    (a (n + 1) : ℂ) = (1 / 96) * (-3 * (-1 + (-1) ^ n + 4 * I * (-I) ^ n - 4 * I * I ^ n)
      + (7 - 15 * (-1) ^ n) * n + 3 * (-1 + (-1) ^ n) * n ^ 2 + 2 * n ^ 3) := by
  sorry

end OMA.S_oeis_a293821
