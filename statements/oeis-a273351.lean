import Mathlib

/-!
# A273351: Number of up steps in all bargraphs of semiperimeter n (n>=2).

Source: https://oeis.org/A273351
Credit: @vivanpoddar

The sequence (offset 2) begins 1, 3, 10, 32, 102, 326, 1046, 3370, 10899, ...
The entry gives the generating function
  (1-z-z^2-z^3-(1+z)*h)/(2*h), where h = sqrt(1-4*z+2*z^2+z^4)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 + 2*x^2 - 4*x + 1 the series is, in normalised form,
  (-x^5 - x^4 - 2*x^3 + 2*x^2 + 3*x - 1 + (-x^3 - x^2 - x + 1)*sqrt(R)) / (2*x^4 + 4*x^2 - 8*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 06 2016) reads
  Conjecture: n*(13*n-40)*a(n) +(-55*n^2+211*n-129)*a(n-1) +(38*n^2-212*n+255)*a(n-2) +(-6*n^2+56*n-75)*a(n-3) +(13*n^2-66*n+3)*a(n-4) -(3*n-13)*(n-6)*a(n-5)=0
It involves a(n-5) and the offset is 2, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a273351

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 2 * X ^ 2 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A273351: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 + 3 * X + 2 * X ^ 2 - 2 * X ^ 3 - X ^ 4 - X ^ 5 + (1 - X - X ^ 2 - X ^ 3) * S)
      * (2 - 8 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A273351. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (13 * (n : ℚ) ^ 2 - 40 * (n : ℚ)) * a n
      + (-55 * (n : ℚ) ^ 2 + 211 * (n : ℚ) - 129) * a (n - 1)
      + (38 * (n : ℚ) ^ 2 - 212 * (n : ℚ) + 255) * a (n - 2)
      + (-6 * (n : ℚ) ^ 2 + 56 * (n : ℚ) - 75) * a (n - 3)
      + (13 * (n : ℚ) ^ 2 - 66 * (n : ℚ) + 3) * a (n - 4)
      + (-3 * (n : ℚ) ^ 2 + 31 * (n : ℚ) - 78) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a273351
