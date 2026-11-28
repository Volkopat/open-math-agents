import Mathlib

/-!
# A221574: Number of 0..n arrays of length 3 with each element differing from at least one neighbor by something other than 1.

Source: https://oeis.org/A221574
Credit: @agchua

Colin Barker (Aug 08 2018), in the formula section of A221574:
  Conjectures from Colin Barker, Aug 08 2018: (Start)
  G.f.: x*(2 + x)*(1 + x^2) / (1 - x)^4.
  a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>3. (End)
The offset is 1 (the data 2, 9, 26, 59, ... start at n = 1), so the g.f. is the series of a(n) x^n
over n ≥ 1; it is stated as an identity of formal power series over ℚ:
(∑_{n ≥ 1} a(n) X^n) * (1 - X)^4 = X * (2 + X) * (1 + X^2).
At n = 4 the recurrence would use a(0), which is not a term; with the value 0 that the g.f. gives at
x^0 it fails there (4*26 - 6*9 + 4*2 - 0 = 58, but a(4) = 59), as it does with the count 1 of the one
array for n = 0. So the recurrence is stated for n ≥ 5, where all its indices are terms.
Definition: an array is (x0, x1, x2) with entries in 0..n; x0 and x2 have the one neighbor x1, and
x1 has the neighbors x0 and x2; u differs from v by something other than 1 means that neither
u = v + 1 nor v = u + 1.
-/

namespace OMA.S_oeis_a221574

/-- A221574(n): the number of (x0, x1, x2) with entries in 0..n such that x0 differs from x1, x1
differs from x0 or from x2, and x2 differs from x1, by something other than 1. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ (Finset.range (n + 1) ×ˢ Finset.range (n + 1))).filter
    (fun x : ℕ × ℕ × ℕ =>
      ¬ (x.1 = x.2.1 + 1 ∨ x.2.1 = x.1 + 1) ∧
      (¬ (x.2.1 = x.1 + 1 ∨ x.1 = x.2.1 + 1) ∨ ¬ (x.2.1 = x.2.2 + 1 ∨ x.2.2 = x.2.1 + 1)) ∧
      ¬ (x.2.2 = x.2.1 + 1 ∨ x.2.1 = x.2.2 + 1))).card

/-- Barker's conjectures: the recurrence (for n ≥ 5) and the g.f. x(2+x)(1+x^2)/(1-x)^4 (for the
terms, n ≥ 1). -/
theorem main : (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 4 =
      PowerSeries.X * (2 + PowerSeries.X) * (1 + PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a221574
