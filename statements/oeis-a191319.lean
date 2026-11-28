import Mathlib

/-!
# A191319: Sum of pyramid weights of all dispersed Dyck paths of length n (i.e., of all Motzkin paths of length n with no (1,0) steps at positive heights).

Source: https://oeis.org/A191319
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 2, 7, 14, 37, 74, 177, ...
The entry gives the generating function
  z^2/((1-2*z)*(1-z^2)*sqrt(1-4*z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (0 + (x^2)*sqrt(R)) / (-8*x^5 + 4*x^4 + 10*x^3 - 5*x^2 - 2*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Dec 07 2017) reads
  Conjecture: (-n+2)*a(n) +2*a(n-1) +5*(n-2)*a(n-2) -2*a(n-3) +4*(-n+2)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a191319

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191319: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    (((X ^ 2) * S)
      * (1 - 2 * X - 5 * X ^ 2 + 10 * X ^ 3 + 4 * X ^ 4 - 8 * X ^ 5 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191319. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-(n : ℚ) + 2) * a n + (2) * a (n - 1) + (5 * (n : ℚ) - 10) * a (n - 2) + (-2) * a (n - 3)
      + (-4 * (n : ℚ) + 8) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a191319
