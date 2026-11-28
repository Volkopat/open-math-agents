import Mathlib

/-!
# A278472: a(n) = Sum_{i=0..n} Fibonacci(i+1)*binomial(2*n-i+2, n+2).

Source: https://oeis.org/A278472
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 5, 22, 92, 376, 1518, 6085, 24285, 96647, ...
The entry gives the generating function
  -(2*x+sqrt(1-4*x)-1)/((2*sqrt(1-4*x)*x-8*x+2)*x^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (4*x^2 - 5*x + 1 + (2*x^2 + 3*x - 1)*sqrt(R)) / (8*x^5 + 30*x^4 - 16*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Mar 06 2017) reads
  Conjecture: +(n+2)*(n^2-4*n+1)*a(n) +2*(-4*n^3+9*n^2+16*n-6)*a(n-1) +(15*n^3-38*n^2-9*n+14)*a(n-2) +2*(2*n-1)*(n^2-2*n-2)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a278472

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A278472: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 5 * X + 4 * X ^ 2 + (-1 + 3 * X + 2 * X ^ 2) * S)
      * (2 - 16 * X + 30 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A278472. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) ^ 3 - 2 * (n : ℚ) ^ 2 - 7 * (n : ℚ) + 2) * a n
      + (-8 * (n : ℚ) ^ 3 + 18 * (n : ℚ) ^ 2 + 32 * (n : ℚ) - 12) * a (n - 1)
      + (15 * (n : ℚ) ^ 3 - 38 * (n : ℚ) ^ 2 - 9 * (n : ℚ) + 14) * a (n - 2)
      + (4 * (n : ℚ) ^ 3 - 10 * (n : ℚ) ^ 2 - 4 * (n : ℚ) + 4) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a278472
