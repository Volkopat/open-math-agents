import Mathlib

/-!
# A254314: Hankel transform of a(n) is A006720(n). Hankel transform of a(n+1) is A006720(n+2).

Source: https://oeis.org/A254314
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 5, 14, 43, 143, 507, 1887, ...
The entry gives the generating function
  (3 - 6*x + x^2 - sqrt( (1-4*x+x^2)^2 - 4*x^3 )) / (2*(1 - 2*x))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 12*x^3 + 18*x^2 - 8*x + 1 the series is, in normalised form,
  (x^2 - 6*x + 3 + (-1)*sqrt(R)) / (2 - 4*x),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 07 2016) reads
  Conjecture: n*a(n) +2*(-5*n+6)*a(n-1) +2*(17*n-39)*a(n-2) +6*(-8*n+27)*a(n-3) +(25*n-114)*a(n-4) +2*(-n+6)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a254314

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X + 18 * X ^ 2 - 12 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A254314: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((3 - 6 * X + X ^ 2 - S)
      * (2 - 4 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A254314. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℚ) * a n + (-10 * (n : ℚ) + 12) * a (n - 1) + (34 * (n : ℚ) - 78) * a (n - 2)
      + (-48 * (n : ℚ) + 162) * a (n - 3) + (25 * (n : ℚ) - 114) * a (n - 4)
      + (-2 * (n : ℚ) + 12) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a254314
