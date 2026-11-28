import Mathlib

/-!
# A322598: Barker's generating function and recurrence

Source: https://oeis.org/A322598
Credit: @ivillar

Status: known result. The entry records the g.f. and the recurrence (Colin Barker, Dec 19 2018) and
then Robert Israel's formulas for a(6*m+r), r = 0..5 (Dec 19 2018), with the note that these imply
the conjectured G.f. and recursion. Here both are derived from the closed form recorded in the entry,
which is used as the definition.

A322598 (offset 1): a(n) is the number of unlabeled rank-3 graded lattices with 3 coatoms and n
atoms; data 1, 3, 8, 13, 20, 29, 39, 50, 64, 78, 94, 112, 131, 151, 174, 197, 222, 249, 277, 306, ...

From Colin Barker, Dec 19 2018:
(1) G.f.: x*(1 + 2*x + 4*x^2 + 2*x^3) / ((1 - x)^3*(1 + x)*(1 + x + x^2)).
(2) a(n) = a(n-1) + a(n-2) - a(n-4) - a(n-5) + a(n-6) for n>6.

Formalization: the entry records a(n) = floor( (3/4)n^2 + (1/3)n + 1/4 ), which is
floor((9n^2 + 4n + 3)/12); this is the definition of a(n) used here (integer floor division). It
gives a(0) = 0, in agreement with the g.f., which has no constant term. (1) is stated with the
denominator cleared, as an identity of formal power series over ℚ. (2) is stated for n ≥ 7.
`main` is the conjunction.
-/

namespace OMA.S_oeis_a322598

open PowerSeries

/-- a(n) = floor((9n^2 + 4n + 3)/12) = floor((3/4)n^2 + (1/3)n + 1/4), as recorded in the entry. -/
def a (n : ℕ) : ℤ := (9 * (n : ℤ) ^ 2 + 4 * (n : ℤ) + 3) / 12

/-- The g.f. and the recurrence of Colin Barker for A322598. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 + X + X ^ 2)) =
      X * (1 + 2 * X + 4 * X ^ 2 + 2 * X ^ 3)) ∧
    (∀ n : ℕ, 7 ≤ n → a n = a (n - 1) + a (n - 2) - a (n - 4) - a (n - 5) + a (n - 6)) := by
  sorry

end OMA.S_oeis_a322598
