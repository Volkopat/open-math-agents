import Mathlib

/-!
# A186341: a(n)=sum{k=0..floor(n/2), binomial(n-k,k)*A186338(k)}.

Source: https://oeis.org/A186341
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 3, 5, 15, 33, 95, 237, 667, ...
The entry gives the generating function
  (1-x-3x^2-sqrt((1-3x-7x^2+19x^3+15x^4-25x^5-16x^6)/(1-x)))/(2x^2(1-x-2x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = (x - 1)*(x^2 + x - 1)*(16*x^4 + 9*x^3 - 8*x^2 - 2*x + 1) the series is, in normalised form,
  (3*x^3 - 2*x^2 - 2*x + 1 + (-1)*sqrt(R)) / (4*x^5 - 2*x^4 - 4*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 08 2016) reads
  Conjecture: (n+2)*a(n) +5*(-n-1)*a(n-1) +2*(-n+3)*a(n-2) +(38*n-59)*a(n-3) +(-22*n+41)*a(n-4) +4*(-22*n+81)*a(n-5) +3*(19*n-79)*a(n-6) +3*(29*n-164)*a(n-7) +2*(-17*n+98)*a(n-8) +16*(-2*n+15)*a(n-9)=0
It involves a(n-9) and the offset is 0, so it is stated for n >= 9.
-/

namespace OMA.S_oeis_a186341

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X - 4 * X ^ 2 + 26 * X ^ 3 - 4 * X ^ 4 - 40 * X ^ 5 + 9 * X ^ 6 + 16 * X ^ 7

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A186341: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - S)
      * (2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A186341. -/
theorem main : ∀ n : ℕ, 9 ≤ n →
    ((n : ℚ) + 2) * a n + (-5 * (n : ℚ) - 5) * a (n - 1) + (-2 * (n : ℚ) + 6) * a (n - 2)
      + (38 * (n : ℚ) - 59) * a (n - 3) + (-22 * (n : ℚ) + 41) * a (n - 4)
      + (-88 * (n : ℚ) + 324) * a (n - 5) + (57 * (n : ℚ) - 237) * a (n - 6)
      + (87 * (n : ℚ) - 492) * a (n - 7) + (-34 * (n : ℚ) + 196) * a (n - 8)
      + (-32 * (n : ℚ) + 240) * a (n - 9) = 0 := by
  sorry

end OMA.S_oeis_a186341
