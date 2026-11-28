import Mathlib

/-!
# A039827: Number of different coefficient values in expansion of Product (1+q^i+q^(2i)), i=1 to n.

Source: https://oeis.org/A039827
Credit: @rtflynn

Chai Wah Wu (Jun 22 2016), in the formula section of A039827:
  Conjectures: a(n) = n*(n+1)/2 - 1 for n >= 9. a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n > 11.
  G.f.: x*(-x^10 + 2*x^9 - x^8 - 2*x^7 + 4*x^6 - x^5 - 2*x^3 + x - 1)/(x - 1)^3.

Conventions:
* The product is the polynomial `P n = ∏_{i=1..n} (1 + q^i + q^(2i))` in `Polynomial ℕ`. Its
  expansion has the coefficients of q^0, ..., q^d with d = `natDegree (P n)` (= n(n+1)); the
  different coefficient values are the image of `coeff (P n)` on `Finset.range (d + 1)`.
  (For n ≥ 1 none of these coefficients is 0, so this is also the set of values of the nonzero
  coefficients.)
* Offset 1. The definition also gives a value at n = 0 (P 0 = 1), which is not a term: the g.f.
  is stated for the series with constant term 0 and coefficient a(n) at X^n for n ≥ 1, as an
  identity of formal power series over ℚ, (∑ a(n) X^n) * (X - 1)^3 = numerator.
* The closed form is stated in ℕ (n(n+1)/2 is an exact division and the value is ≥ 1 for n ≥ 9),
  the recurrence in ℤ for every n ≥ 12 (n > 11).

Numerical check: a Python copy of the definition gives 1, 2, 3, 6, 11, 19, 26, 34, 44, 54, 65,
77, 90, 104, 119 for n = 1..15, the DATA of the entry.
-/

namespace OMA.S_oeis_a039827

open Polynomial

/-- The product (1 + q + q^2)(1 + q^2 + q^4) ⋯ (1 + q^n + q^(2n)). -/
noncomputable def P (n : ℕ) : ℕ[X] := ∏ i ∈ Finset.Icc 1 n, (1 + X ^ i + X ^ (2 * i))

/-- A039827: the number of different coefficient values of `P n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range ((P n).natDegree + 1)).image (P n).coeff).card

/-- Wu's conjectures: the closed form for n ≥ 9, the recurrence for n > 11 and the g.f. -/
theorem main : (∀ n : ℕ, 9 ≤ n → a n = n * (n + 1) / 2 - 1) ∧
    (∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (PowerSeries.X - 1) ^ 3 =
      PowerSeries.X * (-PowerSeries.X ^ 10 + 2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 8 -
        2 * PowerSeries.X ^ 7 + 4 * PowerSeries.X ^ 6 - PowerSeries.X ^ 5 -
        2 * PowerSeries.X ^ 3 + PowerSeries.X - 1) := by
  sorry

end OMA.S_oeis_a039827
