import Mathlib

/-!
# A147817: two conjectured formulas

Source: https://oeis.org/A147817
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both
statements follow from the closed form recorded in the entry, which is used as the definition here.

A147817 (offset 4): number of consistent sets of 4 irreflexive binary order relationships over n objects;
data 186, 3050, 20790, 93030, 321580, 930636, 2362500, 5420580, 11473110, 22732710, ...

Conjectures from Colin Barker, Apr 11 2020:
(1) G.f.: 2*x^4*(93 + 688*x + 18*x^2 + 48*x^3 - 7*x^4) / (1 - x)^9.
(2) a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>10.

Formalization: the entry records the closed form
a(n) = binomial(n,4) * (n^4 + 2*n^3 - 5*n^2 - 22*n - 30) (Vaclav Kotesovec, Apr 11 2020),
and this formula, with values in ℤ, is the definition of a(n) used here for all n ≥ 0 (it vanishes
for n < 4, in agreement with the offset and with a g.f. starting at x^4). The g.f. conjecture is
stated as the identity (Sum_n a(n) x^n) * (1 - x)^9 = (numerator) of formal power series over ℚ. The
recurrence is proved for every n ≥ 9, a range that contains the stated range n > 10. `main` is the
conjunction of (1) and (2).
-/

namespace OMA.S_oeis_a147817

open PowerSeries

/-- The closed form recorded in the entry. -/
def a (n : ℕ) : ℤ := (n.choose 4 : ℤ) * ((n : ℤ) ^ 4 + 2 * (n : ℤ) ^ 3 - 5 * (n : ℤ) ^ 2 - 22 * (n : ℤ) - 30)

/-- The two conjectures of Colin Barker for A147817. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 9 = 2 * X ^ 4 * (93 + 688 * X + 18 * X ^ 2 + 48 * X ^ 3 - 7 * X ^ 4)) ∧
    (∀ n : ℕ, 9 ≤ n → a n = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a147817
