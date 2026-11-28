import Mathlib

/-!
# A098521: E.g.f. exp(x)*BesselI(2,2*sqrt(2)*x)/2.

Source: https://oeis.org/A098521
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 3, 14, 50, 195, 721, 2716, ...
The entry gives the generating function
  (1-2*x-3*x^2-(1-x)*sqrt(1-2*x-7*x^2))/(8*x^2*sqrt(1-2*x-7*x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -7*x^2 - 2*x + 1 the series is, in normalised form,
  (-7*x^3 + 5*x^2 + 3*x - 1 + (-3*x^2 - 2*x + 1)*sqrt(R)) / (-56*x^4 - 16*x^3 + 8*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Dec 08 2011) reads
  Conjecture: (n+2)*a(n) -(4n+3)*a(n-1) -3*(2n+1)*a(n-2) +(20n-29)*a(n-3) +21*(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a098521

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 7 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A098521: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-1 + 3 * X + 5 * X ^ 2 - 7 * X ^ 3 + (1 - 2 * X - 3 * X ^ 2) * S)
      * (8 - 16 * X - 56 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A098521. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 2) * a n + (-4 * (n : ℚ) - 3) * a (n - 1) + (-6 * (n : ℚ) - 3) * a (n - 2)
      + (20 * (n : ℚ) - 29) * a (n - 3) + (21 * (n : ℚ) - 63) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a098521
