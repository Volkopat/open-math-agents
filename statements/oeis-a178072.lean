import Mathlib

/-!
# A178072: Sequence with Hankel transform equal to the Somos-4 sequence A006769(n+2).

Source: https://oeis.org/A178072
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, -1, -1, -1, -1, 1, 8, 23, ...
The entry gives the generating function
  2 / (1 + 2*x + x^2 + sqrt(1 - 4*x + 6*x^2 + x^4))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 + 6*x^2 - 4*x + 1 the series is, in normalised form,
  (x^2 + 2*x + 1 + (-1)*sqrt(R)) / (2*x^3 + 4*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: 2*n*(n+1)*a(n) +2*n*(n+1)*a(n-1) -3*(3*n-1)*(3*n-4)*a(n-2) +(61*n^2-191*n+36)*a(n-3) +6*(-2*n^2+2*n-1)*a(n-4) +2*(5*n-1)*(4*n-15)*a(n-5) +n*(n-5)*a(n-6) +(5*n-1)*(n-6)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a178072

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 6 * X ^ 2 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A178072: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 + 2 * X + X ^ 2 - S)
      * (4 + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A178072. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (2 * (n : ℚ) ^ 2 + 2 * (n : ℚ)) * a n + (2 * (n : ℚ) ^ 2 + 2 * (n : ℚ)) * a (n - 1)
      + (-27 * (n : ℚ) ^ 2 + 45 * (n : ℚ) - 12) * a (n - 2)
      + (61 * (n : ℚ) ^ 2 - 191 * (n : ℚ) + 36) * a (n - 3)
      + (-12 * (n : ℚ) ^ 2 + 12 * (n : ℚ) - 6) * a (n - 4)
      + (40 * (n : ℚ) ^ 2 - 158 * (n : ℚ) + 30) * a (n - 5)
      + ((n : ℚ) ^ 2 - 5 * (n : ℚ)) * a (n - 6)
      + (5 * (n : ℚ) ^ 2 - 31 * (n : ℚ) + 6) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a178072
