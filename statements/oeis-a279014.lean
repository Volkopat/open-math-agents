import Mathlib

/-!
# A279014: a(n) = Sum_{k=0..n} fibonacci(k+1)*binomial(2*n-1,n-k).

Source: https://oeis.org/A279014
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 8, 33, 138, 581, 2455, 10395, 44068, ...
The entry gives the generating function
  (2*x)/(((-(1-sqrt(1-4*x))/(1+sqrt(1-4*x))-((1-sqrt(1-4*x))/(1+sqrt(1-4*x)))^2)+1)*(1-sqrt(1-4*x))*sqrt(1-4*x))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (4*x^3 + 7*x^2 - 6*x + 1 + (x^2 - 4*x + 1)*sqrt(R)) / (8*x^3 + 30*x^2 - 16*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Mar 12 2017) reads
  Conjecture: +n*(3*n-62)*a(n) +(3*n^2+362*n-247)*a(n-1) +(-171*n^2+220*n+162)*a(n-2) +(417*n^2-2570*n+3551)*a(n-3) +2*(27*n-59)*(2*n-7)*a(n-4)=0
The recurrence fails for n in [4] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a279014

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A279014: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 6 * X + 7 * X ^ 2 + 4 * X ^ 3 + (1 - 4 * X + X ^ 2) * S)
      * (2 - 16 * X + 30 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A279014. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (3 * (n : ℚ) ^ 2 - 62 * (n : ℚ)) * a n + (3 * (n : ℚ) ^ 2 + 362 * (n : ℚ) - 247) * a (n - 1)
      + (-171 * (n : ℚ) ^ 2 + 220 * (n : ℚ) + 162) * a (n - 2)
      + (417 * (n : ℚ) ^ 2 - 2570 * (n : ℚ) + 3551) * a (n - 3)
      + (108 * (n : ℚ) ^ 2 - 614 * (n : ℚ) + 826) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a279014
