import Mathlib

/-!
# A191790: Number of base pyramids in all length n left factors of Dyck paths.

Source: https://oeis.org/A191790
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 1, 4, 5, 14, 20, 49, ...
The entry gives the generating function
  z^2*c^2/((1-z^2)*(1-z*c)), where c = (1-sqrt(1-4*z^2))/(2*z^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (2*x^2 + x - 1 + (1 - x)*sqrt(R)) / (4*x^4 - 2*x^3 - 4*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: (n+1)*a(n) +(-n-1)*a(n-1) +5*(-n+1)*a(n-2) +(5*n-11)*a(n-3) +2*(2*n-3)*a(n-4) +4*(-n+3)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a191790

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191790: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + X + 2 * X ^ 2 + (1 - X) * S)
      * (2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191790. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 1) * a n + (-(n : ℚ) - 1) * a (n - 1) + (-5 * (n : ℚ) + 5) * a (n - 2)
      + (5 * (n : ℚ) - 11) * a (n - 3) + (4 * (n : ℚ) - 6) * a (n - 4)
      + (-4 * (n : ℚ) + 12) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a191790
