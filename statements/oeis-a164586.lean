import Mathlib

/-!
# A164586: Row sums of generalized rhombic triangle A164585.

Source: https://oeis.org/A164586
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 3, 8, 19, 51, 134, 354, 952, ...
The entry gives the generating function
  (1-2*x-2*x^2-x^3- sqrt(1-4*x^2-10*x^3-4*x^4+x^6))/(2*x*(x^4+3*x^3+4*x^2+x-1))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^6 - 4*x^4 - 10*x^3 - 4*x^2 + 1 the series is, in normalised form,
  (x^3 + 2*x^2 + 2*x - 1 + (1)*sqrt(R)) / (-2*x^5 - 6*x^4 - 8*x^3 - 2*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Feb 10 2015) reads
  Conjecture: (n+1)*a(n) +(n-1)*a(n-1) +2*(-2*n-1)*a(n-2) +2*(-7*n+10)*a(n-3) +14*(-n+2)*a(n-4) +2*(-2*n+3)*a(n-5) +(n-7)*a(n-6) +(n-5)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a164586

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2 - 10 * X ^ 3 - 4 * X ^ 4 + X ^ 6

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A164586: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 2 * X + 2 * X ^ 2 + X ^ 3 + S)
      * (2 - 2 * X - 8 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A164586. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℚ) + 1) * a n + ((n : ℚ) - 1) * a (n - 1) + (-4 * (n : ℚ) - 2) * a (n - 2)
      + (-14 * (n : ℚ) + 20) * a (n - 3) + (-14 * (n : ℚ) + 28) * a (n - 4)
      + (-4 * (n : ℚ) + 6) * a (n - 5) + ((n : ℚ) - 7) * a (n - 6)
      + ((n : ℚ) - 5) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a164586
