import Mathlib

/-!
# A217333: G.f.: exp( Sum_{n>=1} x^n/n * Sum_{k=0..n} binomial(n,k)^2 * x^k/(1-x)^k ).

Source: https://oeis.org/A217333
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 5, 12, 29, 72, 182, 466, ...
The entry gives the generating function
  (1-2*x - sqrt(1-4*x+4*x^2-4*x^3+4*x^4))/(2*x^3)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^4 - 4*x^3 + 4*x^2 - 4*x + 1 the series is, in normalised form,
  (1 - 2*x + (-1)*sqrt(R)) / (2*x^3),
which is the expression used below (the division by x^3 is the shift of the index by 3).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, May 17 2019) reads
  Conjecture: (n+3)*a(n) +2*(-2*n-3)*a(n-1) +4*n*a(n-2) +2*(-2*n+3)*a(n-3) +4*(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a217333

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 4 * X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A217333: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 3)
    ((1 - 2 * X - S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A217333. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 3) * a n + (-4 * (n : ℚ) - 6) * a (n - 1) + (4 * (n : ℚ)) * a (n - 2)
      + (-4 * (n : ℚ) + 6) * a (n - 3) + (4 * (n : ℚ) - 12) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a217333
