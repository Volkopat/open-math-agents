import Mathlib

/-!
# A205342: Number of length 5 nonnegative integer arrays starting and ending with 0 with adjacent elements unequal but differing by no more than n.

Source: https://oeis.org/A205342
Credit: @agchua

Colin Barker (Jun 11 2018), in the formula section of A205342:
  Conjectures from Colin Barker, Jun 11 2018: (Start)
  G.f.: x*(2 + 3*x + 3*x^2) / (1 - x)^4.
  a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
  (End)
This file states both parts: the recurrence for n > 4 (offset 1, so all indices are terms), and
the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * (1 - X)^4 = X * (2 + 3X + 3X^2); its coefficient of X^0 is a(0), which the
definition below makes 0 (for n = 0 adjacent entries cannot differ), in accordance with the
factor x of the g.f. (offset 1).
Definition: the arrays are (0, x, y, z, 0) with x, y, z nonnegative integers, adjacent entries
unequal and differing by at most n. Every entry of such an array is at most 2n (x and z are
within n of 0, and y is within n of x), so x, y, z may be taken from 0 .. 2n.
-/

namespace OMA.S_oeis_a205342

/-- Adjacent entries u, v: unequal and differing by at most n. -/
abbrev adj (n u v : ℕ) : Prop := u ≠ v ∧ u ≤ v + n ∧ v ≤ u + n

/-- A205342: the number of arrays (0, x, y, z, 0) of nonnegative integers whose adjacent entries
are unequal and differ by at most n (all entries are at most 2n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    (fun t : ℕ × ℕ × ℕ => adj n 0 t.1 ∧ adj n t.1 t.2.1 ∧ adj n t.2.1 t.2.2 ∧ adj n t.2.2 0)).card

/-- Colin Barker's conjectures: a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4) for n > 4, and the
g.f. x(2 + 3x + 3x^2)/(1 - x)^4. -/
theorem main : (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 4 =
      PowerSeries.X * (2 + 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a205342
