import Mathlib

/-!
# OEIS A293822: pentagons of perimeter n modulo rotation

Source: https://oeis.org/A293822
Credit: Sudharsan Rajendiran

A293822(n) is the number of integer-sided pentagons having perimeter `n`, modulo rotations but
not reflections (a polygon is nondegenerate exactly when its longest side is shorter than `n/2`).
Colin Barker conjectured (Nov 2017) the g.f.
`x^5(1 + x - x^2 + 2x^3 + 7x^4 + 2x^5 - 2x^6 + x^8) / ((1 - x)^5 (1 + x)^4 (1 + x + x^2 + x^3 + x^4))`.
We state it as an identity of formal power series over `ℚ` (after clearing the denominator), with
`a(n)` defined for every `n ≥ 0` (it is `0` for `n < 5`, matching the factor `x^5`).

Conventions: a pentagon is a side sequence `v : Fin 5 → ℕ` in cyclic order with positive sides,
sum `n` and `2 * v i < n` for all `i`; two are equal modulo rotation iff one is a cyclic shift of the
other.
-/

namespace OMA.S_oeis_a293822

/-- Integer-sided pentagons with perimeter `n`: side sequences `v 0, …, v 4` (in cyclic order) of
positive integers with sum `n` and every side shorter than `n / 2` (equivalently, shorter than the
sum of the other four sides). -/
def Q (n : ℕ) : Finset (Fin 5 → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (n + 1)).filter
    (fun v => (∀ i, 0 < v i ∧ 2 * v i < n) ∧ ∑ i, v i = n)

open Classical in
/-- A293822(n): the number of such pentagons modulo rotations (`w ~ v` iff `w i = v (i + k)` for
some `k`, indices mod 5), but not reflections. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Q n).image (fun v => (Q n).filter (fun w => ∃ k : Fin 5, w = fun i => v (i + k)))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) *
        ((1 - X) ^ 5 * (1 + X) ^ 4 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
      X ^ 5 * (1 + X - X ^ 2 + 2 * X ^ 3 + 7 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6 + X ^ 8) := by
  sorry

end OMA.S_oeis_a293822
