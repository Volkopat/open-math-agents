import Mathlib

/-!
# A269410: Number of length-4 0..n arrays with no repeated value greater than or equal to the previous repeated value.

Source: https://oeis.org/A269410
Credit: @agchua

Colin Barker (Jan 21 2019), in the formula section of A269410:
  Conjectures from Colin Barker, Jan 21 2019: (Start)
  G.f.: 3*x*(3 + 6*x - x^2) / (1 - x)^5.
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
  (End)
This file states both parts: the recurrence for n > 5 (offset 1, so all indices are terms), and
the g.f. as an identity of formal power series over ℚ, (∑ a(n) X^n) * (1 - X)^5 = 3X(3 + 6X - X^2);
its coefficient of X^0 is a(0), which the definition below makes 0 (for n = 0 the only array is
(0, 0, 0, 0), whose repeated values are not decreasing), in accordance with the factor x of the
g.f. (offset 1).
Definition: an array (w, x, y, z) with entries in 0..n has a repeated value at each place where an
entry equals the next one: the value w if w = x, the value x if x = y, the value y if y = z. The
condition is that no repeated value is greater than or equal to an earlier repeated value (this is
the same as comparing each with the previous one, since the condition makes the repeated values
strictly decreasing). This reading reproduces the listed values 9, 63, 222, 570, 1215, ... for
n = 1, 2, 3, ... (checked up to n = 13), and the 16 example arrays for n = 8 satisfy it.
-/

namespace OMA.S_oeis_a269410

/-- The array (w, x, y, z): no repeated value (at w = x, x = y or y = z) is greater than or equal
to an earlier repeated value. -/
abbrev ok (w x y z : ℕ) : Prop :=
  ¬ (w = x ∧ x = y ∧ w ≤ x) ∧ ¬ (w = x ∧ y = z ∧ w ≤ y) ∧ ¬ (x = y ∧ y = z ∧ x ≤ y)

/-- A269410: the number of arrays (w, x, y, z) with entries in 0..n that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ × ℕ => ok t.1 t.2.1 t.2.2.1 t.2.2.2)).card

/-- Barker's conjectures: a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5) for n > 5, and
the g.f. 3x(3 + 6x - x^2)/(1 - x)^5. -/
theorem main : (∀ n : ℕ, 6 ≤ n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 5 =
      3 * PowerSeries.X * (3 + 6 * PowerSeries.X - PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a269410
