import Mathlib

/-!
# A298267: two conjectured formulas

Source: https://oeis.org/A298267
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both
statements follow from the closed form recorded in the entry (read with the index shift explained
below), which is used as the definition here.

A298267 (offset 0): a(n) is the maximum number of heptiamonds in a hexagon of order n;
data 0, 3, 7, 13, 21, 30, 42, 54, 69, 85, 103, 123, 144, 168, 192, 219, 247, 277, 309, 342, ...

Conjectures from Colin Barker, Jan 20 2018:
(1) G.f.: x*(1 + x)*(3 - 2*x + 4*x^2 - 2*x^3 + 3*x^4) / ((1 - x)^3*(1 + x + x^2 + x^3 + x^4 + x^5 + x^6)).
(2) a(n) = 2*a(n-1) - a(n-2) + a(n-7) - 2*a(n-8) + a(n-9) for n>8.

Formalization: the entry records the closed form a(n) = floor((6*n^2)/7). With the offset 0 of the
entry this formula gives 0, 0, 3, 7, 13, ..., which is the data shifted by one place: the data
0, 3, 7, 13, 21, ... (and the conjectured g.f., which starts 3*x + 7*x^2 + ...) are
floor(6*(n+1)^2/7) for n = 0, 1, 2, .... The form matching the data, a(n) = floor(6*(n+1)^2/7) with
values in ℤ, is the definition of a(n) used here. The g.f. conjecture is stated as the identity
(Sum_n a(n) x^n) * (1 - x)^3 * (1 + x + x^2 + x^3 + x^4 + x^5 + x^6)
  = x*(1 + x)*(3 - 2*x + 4*x^2 - 2*x^3 + 3*x^4)
of formal power series over ℚ. The recurrence involves a(n-9), so it is stated for n ≥ 9, which is the
stated range n > 8. `main` is the conjunction of (1) and (2).
-/

namespace OMA.S_oeis_a298267

open PowerSeries

/-- a(n) = floor(6(n+1)^2/7): the closed form of the entry, indexed to match the data (offset 0). -/
def a (n : ℕ) : ℤ := (6 * ((n : ℤ) + 1) ^ 2) / 7

/-- The two conjectures of Colin Barker for A298267. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) =
      X * (1 + X) * (3 - 2 * X + 4 * X ^ 2 - 2 * X ^ 3 + 3 * X ^ 4)) ∧
    (∀ n : ℕ, 9 ≤ n → a n = 2 * a (n - 1) - a (n - 2) + a (n - 7) - 2 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a298267
