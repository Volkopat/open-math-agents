import Mathlib

/-!
# A210374: Number of 2 X 2 matrices with all terms in {0,1,...,n} and (sum of terms) = n+2.

Source: https://oeis.org/A210374
Credit: @agchua

Colin Barker (Dec 07 2017), in the formula section of A210374:
  Conjectures from Colin Barker, Dec 07 2017: (Start)
  G.f.: x*(4 + 3*x - 12*x^2 + 6*x^3) / (1 - x )^4.
  a(n) = (-36 + 47*n + 12*n^2 + n^3) / 6 for n>0.
  a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
  (End)
This file states all three parts: the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * (1 - X)^4 = X (4 + 3X - 12X^2 + 6X^3); the closed form for n > 0 as written
(it fails at n = 0, where a(0) = 0), compared in ℚ; and the recurrence for n > 4 as written.
The offset is 0. A 2 X 2 matrix [[w, x], [y, z]] is given by its four entries, so the matrices are
counted as quadruples (w, x, y, z) with every entry in Finset.Icc 0 n, as in the entry's
Mathematica program.
-/

namespace OMA.S_oeis_a210374

/-- A210374(n): the number of quadruples (w, x, y, z) in {0, ..., n}^4 with w + x + y + z = n + 2,
that is, of 2 X 2 matrices with all entries in {0, ..., n} and sum of entries n + 2. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n).filter
    (fun t : ℕ × ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2.1 + t.2.2.2 = n + 2)).card

/-- Barker's conjectures: the generating function, the closed form for n > 0, and the recurrence
for n > 4. -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 4 =
      PowerSeries.X * (4 + 3 * PowerSeries.X - 12 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (-36 + 47 * (n : ℚ) + 12 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ)
        - (a (n - 4) : ℤ)) := by
  sorry

end OMA.S_oeis_a210374
