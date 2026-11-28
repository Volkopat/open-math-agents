import Mathlib

/-!
# A147796: two conjectured formulas

Source: https://oeis.org/A147796
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both
statements follow from the closed form of the entry (proved in its comments by Petros Hadjicostas,
Apr 10 2020), which is used as the definition here.

A147796 (offset 3): number of consistent sets of 3 irreflexive binary order relationships over n
objects;
data 6, 152, 940, 3600, 10570, 26096, 56952, 113280, 209550, 365640, 608036, 971152, ...

Conjectures from Colin Barker, Apr 11 2020:
(1) G.f.: 2*x^3*(3 + 55*x + x^2 + x^3) / (1 - x)^7.
(2) a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>8.

Formalization: the entry records a(n) = binomial(n,3) * (n^3 - 5*n - 6), and this formula, with values
in ℤ, is the definition of a(n) used here for all n ≥ 0 (it gives a(0) = a(1) = a(2) = 0, in
agreement with the offset 3 and with a g.f. starting at x^3). The g.f. conjecture is stated as the
identity (Sum_n a(n) x^n) * (1 - x)^7 = 2*x^3*(3 + 55*x + x^2 + x^3) of formal power series over ℚ.
The recurrence is proved for every n ≥ 7, a range that contains the stated range n > 8. `main` is the
conjunction of (1) and (2).
-/

namespace OMA.S_oeis_a147796

open PowerSeries

/-- a(n) = binomial(n,3) * (n^3 - 5n - 6), the closed form recorded in the entry. -/
def a (n : ℕ) : ℤ := (n.choose 3 : ℤ) * ((n : ℤ) ^ 3 - 5 * (n : ℤ) - 6)

/-- The two conjectures of Colin Barker for A147796. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 7 = 2 * X ^ 3 * (3 + 55 * X + X ^ 2 + X ^ 3)) ∧
    (∀ n : ℕ, 7 ≤ n → a n = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a147796
