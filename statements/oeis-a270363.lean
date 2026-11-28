import Mathlib

/-!
# A270363: a(n) = (n+1)*Sum_{k=0..(n-1)/2}((binomial(2*n-3*k-2,n-k-1))/(n-k)).

Source: https://oeis.org/A270363
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 2, 3, 10, 30, 101, 350, 1250, 4548, ...
The entry gives the generating function
  (1-sqrt(1-4*x))/(sqrt(1-4*x)*x-x+2)*((6*x+sqrt(1-4*x)-1)/(4*x+sqrt(1-4*x)-1))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (12*x^3 - 3*x^2 - 4*x + 1 + (-x^2 + 6*x - 1)*sqrt(R)) / (-8*x^4 + 2*x^3 + 8*x^2 - 10*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Mar 22 2016) reads
  Conjecture: n*(7*n^2-17*n-2) *a(n) +(-35*n^3+99*n^2+20*n-120) *a(n-1) +2* (2*n-5) *(7*n^2-3*n-12)*a(n-2) +n*(7*n^2-17*n-2) *a(n-3) +2*-(2*n-5) *(7*n^2-3*n-12) *a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a270363

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A270363: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 4 * X - 3 * X ^ 2 + 12 * X ^ 3 + (-1 + 6 * X - X ^ 2) * S)
      * (2 - 10 * X + 8 * X ^ 2 + 2 * X ^ 3 - 8 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A270363. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (7 * (n : ℚ) ^ 3 - 17 * (n : ℚ) ^ 2 - 2 * (n : ℚ)) * a n
      + (-35 * (n : ℚ) ^ 3 + 99 * (n : ℚ) ^ 2 + 20 * (n : ℚ) - 120) * a (n - 1)
      + (28 * (n : ℚ) ^ 3 - 82 * (n : ℚ) ^ 2 - 18 * (n : ℚ) + 120) * a (n - 2)
      + (7 * (n : ℚ) ^ 3 - 17 * (n : ℚ) ^ 2 - 2 * (n : ℚ)) * a (n - 3)
      + (-28 * (n : ℚ) ^ 3 + 82 * (n : ℚ) ^ 2 + 18 * (n : ℚ) - 120) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a270363
