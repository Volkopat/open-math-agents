import Mathlib

/-!
# A228197: Number of n-edge ordered trees with bicolored boundary edges.

Source: https://oeis.org/A228197
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 8, 36, 160, 692, 2928, 12200, 50304, ...
The entry gives the generating function
  (1 + 4*x^2*B^2*C)/(1 - 2*x), where C = (1 - sqrt(1 - 4*x))/(2*x) is the Catalan g.f. and B = (1 - 4*x)^(-1/2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (1 - 2*x + (-2*x)*sqrt(R)) / (8*x^2 - 6*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Aug 25 2013) reads
  Conjecture: (-n+1)*a(n) +2*(5*n-8)*a(n-1) +4*(-8*n+17)*a(n-2) +16*(2*n-5)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a228197

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A228197: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 2 * X + (-2 * X) * S)
      * (1 - 6 * X + 8 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A228197. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (-(n : ℚ) + 1) * a n + (10 * (n : ℚ) - 16) * a (n - 1) + (-32 * (n : ℚ) + 68) * a (n - 2)
      + (32 * (n : ℚ) - 80) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a228197
