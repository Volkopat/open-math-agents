import Mathlib

/-!
# A289761: Maximum length of a perfect Wichmann ruler with n segments.

Source: https://oeis.org/A289761
Credit: @agchua

Colin Barker (Jul 14 2017), in the formula section of A289761:
  Conjectures from Colin Barker, Jul 14 2017: (Start)
  G.f.: x^2*(3 + 4*x^5 - 3*x^6) / ((1 - x)^3*(1 + x)*(1 - x + x^2)*(1 + x + x^2)).
  a(n) = 2*a(n-1) - a(n-2) + a(n-6) - 2*a(n-7) + a(n-8) for n>9.
  (End)
This file states both parts: the recurrence for n ≥ 10, as written, and the g.f. as an identity of
formal power series over ℚ (offset 2, so the series starts with a(2) X^2):
(X^2 * Sum_{n ≥ 0} a(n+2) X^n) * (1 - X)^3 (1 + X) (1 - X + X^2) (1 + X + X^2) = X^2 * (3 + 4X^5 - 3X^6).
Definition: the formula line of the entry, a(n) = ( n^2 - (mod(n,6)-3)^2 ) / 3 + n, which the PARI
and Python programs of the entry also compute. The division is exact: n^2 - (n mod 6 - 3)^2 is
divisible by 3 for every n. The formula gives the listed values 3, 6, 9, 12, 15, 22, 29, 36, ...
for n = 2, 3, 4, ...
-/

namespace OMA.S_oeis_a289761

/-- A289761(n) = (n^2 - (n mod 6 - 3)^2)/3 + n (the division is exact). -/
def a (n : ℕ) : ℤ := ((n : ℤ) ^ 2 - ((n : ℤ) % 6 - 3) ^ 2) / 3 + n

/-- Barker's conjectures: the recurrence for n > 9 and the g.f.
x^2 (3 + 4x^5 - 3x^6)/((1 - x)^3 (1 + x) (1 - x + x^2) (1 + x + x^2)). -/
theorem main :
    (∀ n : ℕ, 10 ≤ n →
      a n = 2 * a (n - 1) - a (n - 2) + a (n - 6) - 2 * a (n - 7) + a (n - 8)) ∧
    PowerSeries.X ^ 2 * PowerSeries.mk (fun n => (a (n + 2) : ℚ)) *
        ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) * (1 - PowerSeries.X + PowerSeries.X ^ 2) *
          (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      PowerSeries.X ^ 2 * (3 + 4 * PowerSeries.X ^ 5 - 3 * PowerSeries.X ^ 6) := by
  sorry

end OMA.S_oeis_a289761
