import Mathlib

/-!
# A218832: Number of positive integer solutions to the Diophantine equation x + y + 2z = n^2.

Source: https://oeis.org/A218832
Credit: @rickmanelius

Conjectures from Colin Barker, Apr 01 2013: a(n) = (7 + (-1)^n - 8*n^2 + 2*n^4)/8.
G.f.: -x^2*(x^4 - 4*x^3 + 6*x^2 + 8*x + 1) / ((x-1)^5*(x+1)).

Formalization notes:
* Offset 1. `a n` is the number of triples (x, y, z) of positive integers (natural numbers
  x, y, z > 0) with x + y + 2z = n^2: the `Set.ncard` of the solution set. That set is finite
  (each coordinate is at most n^2), so the count is the true number of solutions. The data
  begin 0, 1, 12, 49, 132, 289, 552, 961, ..., matching the entry (a(3) = 12, as in its
  example).
* The closed form is stated in ℚ, so the division by 8 is exact division. It is stated for
  every n ≥ 1, the indices of the sequence (at the unused index 0 the right side is 1, while
  the equation x + y + 2z = 0 has no positive solutions).
* The g.f. is the series of a(n) x^n over n ≥ 1, stated in `PowerSeries ℤ` with the
  denominator multiplied out: (x-1)^5 (x+1) A(x) = -x^2 (x^4 - 4x^3 + 6x^2 + 8x + 1). The
  denominator has constant term -1, a unit, so the two forms say the same thing. The series
  is `PowerSeries.mk` of the values `a n`; its coefficient at x^0 is the count for n = 0,
  which is 0 (no positive solutions of x + y + 2z = 0), so it is exactly the sum over n ≥ 1.
* The formula a(n) = floor(n^4/4-n^2+1) of the entry is not marked as a conjecture and is
  not stated.
-/

namespace OMA.S_oeis_a218832

/-- A218832: a(n) = the number of positive integer solutions (x, y, z) of x + y + 2z = n^2. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ × ℕ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.1 + p.2.1 + 2 * p.2.2 = n ^ 2}

/-- Barker's conjectures: the closed form for n ≥ 1, and the g.f. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (7 + (-1) ^ n - 8 * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 4) / 8) ∧
    ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) : PowerSeries ℤ) *
        PowerSeries.mk (fun n => (a n : ℤ)) =
      -PowerSeries.X ^ 2 * (PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 2 +
        8 * PowerSeries.X + 1) := by
  sorry

end OMA.S_oeis_a218832
