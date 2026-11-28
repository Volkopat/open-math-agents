import Mathlib

/-!
# A081207: Main diagonal of number square A081206.

Source: https://oeis.org/A081207
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 3, 7, 16, 37, 89, 216, 529, ...
The entry gives the generating function
  (1+x)/sqrt(1-2x-x^2-2x^3+x^4)
(Paul Barry, Jun 04 2005). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (0 + (x + 1)*sqrt(R)) / (x^4 - 2*x^3 - x^2 - 2*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 12 2012) reads
  Conjecture: n*(n-2)*a(n) +(-2*n^2+5*n-1)*a(n-1) +(-n^2+3*n-4)*a(n-2) +(-2*n^2+7*n-4)*a(n-3) +(n-1)*(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a081207

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A081207: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    (((1 + X) * S)
      * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A081207. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) ^ 2 - 2 * (n : ℚ)) * a n + (-2 * (n : ℚ) ^ 2 + 5 * (n : ℚ) - 1) * a (n - 1)
      + (-(n : ℚ) ^ 2 + 3 * (n : ℚ) - 4) * a (n - 2)
      + (-2 * (n : ℚ) ^ 2 + 7 * (n : ℚ) - 4) * a (n - 3)
      + ((n : ℚ) ^ 2 - 4 * (n : ℚ) + 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a081207
