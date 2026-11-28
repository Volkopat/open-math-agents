import Mathlib

/-!
# A026030: a(n) = T(2n,n-1), where T is defined in A026022.

Source: https://oeis.org/A026030
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 4, 15, 56, 209, 780, 2912, 10880, 40698, ...
The entry gives the generating function
  2*x*(1-2*x) / ((1-2*x)*(1-4*x+x^2) + (1-x)*(1-3*x)*sqrt(1-4*x))
(Michael Somos, Jan 08 2012). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (4*x^4 - 20*x^3 + 21*x^2 - 8*x + 1 + (6*x^3 - 11*x^2 + 6*x - 1)*sqrt(R)) / (2*x^5),
which is the expression used below (the division by x^5 is the shift of the index by 5).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 15 2014) reads
  Conjecture: (n+5)*a(n) -2*(5*n+16)*a(n-1) +(35*n+47)*a(n-2) +2*(-25*n+14)*a(n-3) + 12*(2*n-5)*a(n-4) = 0
It involves a(n-4) and the offset is 1, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a026030

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A026030: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 5)
    ((1 - 8 * X + 21 * X ^ 2 - 20 * X ^ 3 + 4 * X ^ 4 + (-1 + 6 * X - 11 * X ^ 2 + 6 * X ^ 3) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A026030. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 5) * a n + (-10 * (n : ℚ) - 32) * a (n - 1) + (35 * (n : ℚ) + 47) * a (n - 2)
      + (-50 * (n : ℚ) + 28) * a (n - 3) + (24 * (n : ℚ) - 60) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026030
