import Mathlib

/-!
# A269411: Number of length-5 0..n arrays with no repeated value greater than or equal to the previous repeated value.

Source: https://oeis.org/A269411
Credit: @agchua

Colin Barker (Jan 21 2019), in the formula section of A269411:
  Conjectures from Colin Barker, Jan 21 2019: (Start)
  G.f.: 3*x*(4 + 29*x + 10*x^2 - 3*x^3) / (1 - x)^6.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.
  (End)
This file states both parts: the recurrence for n > 6 (offset 1, so all indices are terms), and
the g.f. as an identity of formal power series over Q,
(sum of a(n) X^n) * (1 - X)^6 = 3X(4 + 29X + 10X^2 - 3X^3); its coefficient of X^0 is a(0),
which the definition below makes 0 (for n = 0 the only array is 0,0,0,0,0, whose second
repeated value 0 is not less than the first one), in accordance with the factor x of the g.f.
(offset 1).
Definition (R. H. Hardin's convention for these arrays): an array is (x1, x2, x3, x4, x5) with
entries in 0..n. A repeated value is an entry x(i) with x(i) = x(i+1), i = 1..4, and the
repeated values are taken in the order of i. The condition is that no repeated value is
greater than or equal to the previous repeated value, i.e. the repeated values are strictly
decreasing; by transitivity this says: whenever i < j, x(i) = x(i+1) and x(j) = x(j+1), then
x(j) < x(i). These are the six implications of ok below. The definition gives the listed terms
12, 159, 804, 2670, 6960, 15477, 30744 for n = 1..7 (checked by direct enumeration).
-/

namespace OMA.S_oeis_a269411

/-- The condition on the array (x1, x2, x3, x4, x5): for all i < j with x(i) = x(i+1) and
x(j) = x(j+1), the later repeated value x(j) is less than the earlier repeated value x(i). -/
abbrev ok (x1 x2 x3 x4 x5 : ℕ) : Prop :=
  (x1 = x2 → x2 = x3 → x2 < x1) ∧ (x1 = x2 → x3 = x4 → x3 < x1) ∧
  (x1 = x2 → x4 = x5 → x4 < x1) ∧ (x2 = x3 → x3 = x4 → x3 < x2) ∧
  (x2 = x3 → x4 = x5 → x4 < x2) ∧ (x3 = x4 → x4 = x5 → x4 < x3)

/-- A269411: the number of arrays (x1, x2, x3, x4, x5) with entries in 0..n satisfying ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ × ℕ × ℕ => ok t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2)).card

/-- Barker's conjectures: a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)
for n > 6, and the g.f. 3x(4 + 29x + 10x^2 - 3x^3)/(1 - x)^6. -/
theorem main : (∀ n : ℕ, 7 ≤ n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 6 =
      3 * PowerSeries.X * (4 + 29 * PowerSeries.X + 10 * PowerSeries.X ^ 2 -
        3 * PowerSeries.X ^ 3) := by
  sorry

end OMA.S_oeis_a269411
