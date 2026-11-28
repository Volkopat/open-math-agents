import Mathlib

/-!
# A191786: Number of length n left factors of Dyck paths having no triple-rises (triple-rise = three consecutive (1,1)-steps).

Source: https://oeis.org/A191786
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 2, 4, 5, 9, 12, 22, ...
The entry gives the generating function
  2*(1+z+z^2)/(1-z^2-2*z^3+sqrt(1-2*z^2-3*z^4))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^4 - 2*x^2 + 1 the series is, in normalised form,
  (2*x^5 + 3*x^4 + 3*x^3 - x - 1 + (x^2 + x + 1)*sqrt(R)) / (-2*x^6 - 2*x^5 - 2*x^4 + 2*x^3),
which is the expression used below (the division by x^3 is the shift of the index by 3).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -(n+3)*(13*n-70)*a(n) +(-13*n^2+19*n-102)*a(n-1) +(65*n^2-221*n-516) *a(n-2) +(65*n^2-197*n+288)*a(n-3) -(n+6)*(13*n-97) *a(n-4) +3*(-13*n^2+35*n-70) *a(n-5) +(-169*n^2+1201*n-2208) *a(n-6) -9*(13*n-40)*(n-5) *a(n-7) -6*(13*n-25)*(n-6) *a(n-8)=0
It involves a(n-8) and the offset is 0, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a191786

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X ^ 2 - 3 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191786: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 3)
    ((-1 - X + 3 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (1 + X + X ^ 2) * S)
      * (2 - 2 * X - 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191786. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    (-13 * (n : ℚ) ^ 2 + 31 * (n : ℚ) + 210) * a n
      + (-13 * (n : ℚ) ^ 2 + 19 * (n : ℚ) - 102) * a (n - 1)
      + (65 * (n : ℚ) ^ 2 - 221 * (n : ℚ) - 516) * a (n - 2)
      + (65 * (n : ℚ) ^ 2 - 197 * (n : ℚ) + 288) * a (n - 3)
      + (-13 * (n : ℚ) ^ 2 + 19 * (n : ℚ) + 582) * a (n - 4)
      + (-39 * (n : ℚ) ^ 2 + 105 * (n : ℚ) - 210) * a (n - 5)
      + (-169 * (n : ℚ) ^ 2 + 1201 * (n : ℚ) - 2208) * a (n - 6)
      + (-117 * (n : ℚ) ^ 2 + 945 * (n : ℚ) - 1800) * a (n - 7)
      + (-78 * (n : ℚ) ^ 2 + 618 * (n : ℚ) - 900) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a191786
