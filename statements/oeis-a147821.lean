import Mathlib

/-!
# A147821: two conjectured formulas

Source: https://oeis.org/A147821
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both
statements follow from the closed form recorded in the entry, which is used as the definition here.

A147821 (offset 4): number of consistent sets of 5 irreflexive binary order relationships over n objects;
data 108, 6180, 83952, 601944, 2991576, 11662056, 38167920, 109368864, 282174948, 668565612, ...

Conjectures from Colin Barker, Apr 11 2020:
(1) G.f.: 12*x^4*(9 + 416*x + 1826*x^2 + 46*x^3 + 291*x^4 - 78*x^5 + 10*x^6) / (1 - x)^11.
(2) a(n) = 11*a(n-1) - 55*a(n-2) + 165*a(n-3) - 330*a(n-4) + 462*a(n-5) - 462*a(n-6) + 330*a(n-7) - 165*a(n-8) + 55*a(n-9) - 11*a(n-10) + a(n-11) for n>12.

Formalization: the entry records the closed form
a(n) = (n-3)*(n-2)*(n-1)*n*(n^6 + n^5 - 15*n^4 - 45*n^3 - 4*n^2 + 326*n + 900)/120 (Vaclav Kotesovec, Apr 11 2020),
and this formula, with values in ℚ, is the definition of a(n) used here for all n ≥ 0 (it vanishes
for n < 4, in agreement with the offset and with a g.f. starting at x^4). The g.f. conjecture is
stated as the identity (Sum_n a(n) x^n) * (1 - x)^11 = (numerator) of formal power series over ℚ. The
recurrence is proved for every n ≥ 11, a range that contains the stated range n > 12. `main` is the
conjunction of (1) and (2).
-/

namespace OMA.S_oeis_a147821

open PowerSeries

/-- The closed form recorded in the entry. -/
def a (n : ℕ) : ℚ := ((n : ℚ) - 3) * ((n : ℚ) - 2) * ((n : ℚ) - 1) * (n : ℚ) *
    ((n : ℚ) ^ 6 + (n : ℚ) ^ 5 - 15 * (n : ℚ) ^ 4 - 45 * (n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 2 + 326 * (n : ℚ) + 900) / 120

/-- The two conjectures of Colin Barker for A147821. -/
theorem main :
    (PowerSeries.mk a * (1 - X) ^ 11 = 12 * X ^ 4 * (9 + 416 * X + 1826 * X ^ 2 + 46 * X ^ 3 + 291 * X ^ 4 - 78 * X ^ 5 + 10 * X ^ 6)) ∧
    (∀ n : ℕ, 11 ≤ n → a n = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11)) := by
  sorry

end OMA.S_oeis_a147821
