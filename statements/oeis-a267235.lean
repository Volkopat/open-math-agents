import Mathlib

/-!
# A267235: Number of length-6 0..n arrays with no following elements greater than or equal to the first repeated value.

Source: https://oeis.org/A267235
Credit: @agchua

Colin Barker (Jan 10 2019), in the formula section of A267235:
  Conjectures from Colin Barker, Jan 10 2019: (Start)
  G.f.: x*(8 + 167*x + 397*x^2 + 147*x^3 + x^4) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
  (End)
This file states both parts: the recurrence for n > 7 (offset 1, so all indices are terms), and
the g.f. as an identity of formal power series over Q,
(sum of a(n) X^n) * (1 - X)^7 = X(8 + 167X + 397X^2 + 147X^3 + X^4); its coefficient of X^0 is
a(0), which the definition below makes 0 (for n = 0 the only array is 0,0,0,0,0,0, whose first
repeated value 0 is followed by entries 0 that are not less than 0), in accordance with the
factor x of the g.f. (offset 1).
Definition (R. H. Hardin's convention for these arrays): an array is (x1, ..., x6) with entries
in 0..n. Its first repeated value is x(i) for the least i with x(i) = x(i+1), and the elements
following it are x(i+2), ..., x6. The condition is that none of these is greater than or equal
to x(i), i.e. all of them are less than x(i); an array with no two equal adjacent entries
satisfies it. The four implications of ok below say this for i = 1, 2, 3, 4 (for i = 5 no
element follows). The definition gives the listed terms 8, 223, 1790, 8274, 27854 for n = 1..5
(checked by direct enumeration).
-/

namespace OMA.S_oeis_a267235

/-- The condition on the array (x1, ..., x6): if x(i) = x(i+1) is the first pair of equal
adjacent entries, then every entry x(j) with j >= i + 2 is less than x(i). -/
def ok (x1 x2 x3 x4 x5 x6 : ℕ) : Prop :=
  (x1 = x2 → x3 < x1 ∧ x4 < x1 ∧ x5 < x1 ∧ x6 < x1) ∧
  (x1 ≠ x2 → x2 = x3 → x4 < x2 ∧ x5 < x2 ∧ x6 < x2) ∧
  (x1 ≠ x2 → x2 ≠ x3 → x3 = x4 → x5 < x3 ∧ x6 < x3) ∧
  (x1 ≠ x2 → x2 ≠ x3 → x3 ≠ x4 → x4 = x5 → x6 < x4)
instance (x1 x2 x3 x4 x5 x6 : ℕ) : Decidable (ok x1 x2 x3 x4 x5 x6) := by
  unfold ok
  exact instDecidableAnd

/-- A267235: the number of arrays (x1, ..., x6) with entries in 0..n satisfying ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      ok t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2)).card

/-- Barker's conjectures: a(n) = 7a(n-1) - 21a(n-2) + 35a(n-3) - 35a(n-4) + 21a(n-5)
- 7a(n-6) + a(n-7) for n > 7, and the g.f. x(8 + 167x + 397x^2 + 147x^3 + x^4)/(1 - x)^7. -/
theorem main : (∀ n : ℕ, 8 ≤ n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
        21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 7 =
      PowerSeries.X * (8 + 167 * PowerSeries.X + 397 * PowerSeries.X ^ 2 +
        147 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a267235
