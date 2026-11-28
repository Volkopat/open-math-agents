import Mathlib

/-!
# A118974: Sum of the lengths of the first descents in all hill-free Dyck paths of semilength n (a hill in a Dyck path is a peak at level 1).

Source: https://oeis.org/A118974
Credit: @ivillar

Status: false as stated at n = 3 (a(0..3) = 0, 0, 2, 4 and the left side is -144 there); main is the corrected recurrence (n >= 4), which holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 0, 0, 2, 4, 11, 31, 94, 298, 977, ...
The entry gives the generating function
  z^2*C*F*(1+C-z*C)/(1-z), where F = (1-sqrt(1-4*z))/(z*(3-sqrt(1-4*z))) and C = (1-sqrt(1-4*z))/(2*z) is the Catalan function
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X the radicand. Substituting C and F and rationalizing (multiplying by conjugates under sqrt(R) -> -sqrt(R)) gives the form used below.
The series is written as (G) / (C * x^2) with C of nonzero constant term; the division by
x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 22 2016) reads
  Conjecture: 2*(n+1)*(17*n^2-65*n+60)*a(n) -3*(3*n-4)*(17*n^2-48*n+15)*a(n-1) +3*(17*n^3-82*n^2+121*n-60)*a(n-2) +2*(2*n-5) *(17*n^2-31*n+12) *a(n-3)=0.
It involves a(n-3) and fails at n = 3, so the corrected recurrence is stated for n >= 4.
-/

namespace OMA.S_oeis_a118974

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A118974: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4) * S)
      * (8 - 6 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The corrected recurrence for A118974. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (34 * (n : ℚ) ^ 3 - 96 * (n : ℚ) ^ 2 - 10 * (n : ℚ) + 120) * a n
      + (-153 * (n : ℚ) ^ 3 + 636 * (n : ℚ) ^ 2 - 711 * (n : ℚ) + 180) * a (n - 1)
      + (51 * (n : ℚ) ^ 3 - 246 * (n : ℚ) ^ 2 + 363 * (n : ℚ) - 180) * a (n - 2)
      + (68 * (n : ℚ) ^ 3 - 294 * (n : ℚ) ^ 2 + 358 * (n : ℚ) - 120) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a118974
