import Mathlib

/-!
# A114589: Number of hill-free Dyck paths of semilength n+3 and having no peaks at even levels (a hill in a Dyck path is a peak at level 1).

Source: https://oeis.org/A114589
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 3, 7, 17, 43, 110, 286, 753, ...
The entry gives the generating function
  (1 -z -2*z^2 -2*z^3 -sqrt(1-3*z^2-2*z))/(2*z^4*(2+2*z+z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^2 - 2*x + 1 the series is, in normalised form,
  (-2*x^3 - 2*x^2 - x + 1 + (-1)*sqrt(R)) / (2*x^6 + 4*x^5 + 4*x^4),
which is the expression used below (the division by x^4 is the shift of the index by 4).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 02 2018) reads
  Conjecture: 2*(n+4)*a(n) +2*(-n-1)*a(n-1) +3*(-3*n-4)*a(n-2) +(-8*n-11)*a(n-3) +3*(-n-1)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a114589

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A114589: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 4)
    ((1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S)
      * (4 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A114589. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ) + 8) * a n + (-2 * (n : ℚ) - 2) * a (n - 1) + (-9 * (n : ℚ) - 12) * a (n - 2)
      + (-8 * (n : ℚ) - 11) * a (n - 3) + (-3 * (n : ℚ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a114589
